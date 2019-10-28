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
lean_object* l_Lean_Parser_Module_prelude___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__5;
lean_object* l_Lean_Parser_Module_importPath___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_importPath___elambda__1___closed__2;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_importPath___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Parser_whitespace___main(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_importPath___elambda__1___closed__1;
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
lean_object* lean_test_module_parser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_ParserAttribute_runParser(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
lean_object* l_Lean_Parser_Module_importPath___closed__1;
lean_object* l_Lean_Parser_Module_header;
lean_object* l_Lean_Parser_parseFileAux___main___closed__1;
lean_object* l_Lean_Parser_Module_import___closed__2;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l_Lean_Parser_rawCh___elambda__1___rarg(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__1;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7;
lean_object* l_Lean_Parser_Module_header___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh(uint8_t, uint32_t, uint8_t);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
extern lean_object* l_Substring_drop___closed__2;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_importPath___closed__2;
lean_object* l_Lean_Parser_Module_importPath___closed__6;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__2;
lean_object* l_Lean_Parser_testModuleParser___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__2;
lean_object* l___private_Init_Lean_Parser_Module_3__consumeInput(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___closed__1;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__1;
lean_object* l_Lean_Parser_Module_import___closed__3;
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__1;
lean_object* l_Lean_Parser_isEOI___boxed(lean_object*);
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__3;
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___closed__2;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__4;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_importPath___closed__4;
lean_object* l_Lean_Parser_Module_importPath___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__6;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Parser_ident___closed__1;
lean_object* l_Lean_Parser_Module_header___closed__6;
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI(lean_object*);
extern lean_object* l_Lean_mkSearchPathRef___closed__1;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
lean_object* l_Lean_Parser_Module_prelude___closed__2;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_parseCommand___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_testModuleParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__2;
lean_object* l_EState_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__3;
lean_object* l_Lean_Parser_Module_header___closed__5;
extern lean_object* l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_object* l_Lean_Parser_identFn___rarg(lean_object*, lean_object*);
lean_object* lean_io_prim_read_text_file(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
lean_object* l_Lean_Parser_Module_importPath;
lean_object* l_Lean_Parser_Module_prelude___closed__4;
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1;
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object*);
lean_object* l_Lean_Parser_mkParserContextCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseFileAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateLeading___rarg(lean_object*);
lean_object* l_Lean_Parser_parseFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ModuleParserState_inhabited___closed__1;
lean_object* l_Lean_Parser_parseFileAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_Parser_ModuleParserState_inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_EState_pure___rarg(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__5;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__1;
lean_object* l_Lean_Parser_Module_prelude;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__7;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8_t, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__4;
extern lean_object* l_Lean_Parser_Command_exit___elambda__1___rarg___closed__2;
lean_object* l_Lean_Parser_Module_header___closed__4;
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_commandParserAttribute;
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
lean_object* l_Lean_Parser_Module_importPath___closed__5;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_12 = lean_string_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_13, x_5);
x_15 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_19 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_19, x_5);
x_21 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_23 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_23, x_5);
x_25 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
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
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = 46;
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Lean_Parser_rawCh___elambda__1___rarg(x_5, x_9, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_8, x_12);
lean_dec(x_12);
lean_dec(x_8);
if (x_13 == 0)
{
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Parser_manyAux___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_10, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_8, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Parser_ParserState_restore(x_10, x_7, x_8);
lean_dec(x_7);
return x_19;
}
}
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("importPath");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_importPath___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_importPath___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(x_6, x_1, x_2, x_3);
x_8 = l_Lean_nullKind;
lean_inc(x_5);
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Parser_identFn___rarg(x_2, x_9);
x_12 = l_Lean_Parser_Module_importPath___elambda__1___closed__2;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_2);
x_14 = l_Lean_Parser_Module_importPath___elambda__1___closed__2;
x_15 = l_Lean_Parser_ParserState_mkNode(x_9, x_14, x_5);
return x_15;
}
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 46;
x_2 = 0;
x_3 = 1;
x_4 = l_Lean_Parser_rawCh(x_2, x_1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_importPath___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_importPath___closed__2;
x_2 = l_Lean_Parser_ident___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_importPath___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_importPath___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_importPath___elambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_importPath___closed__4;
x_2 = l_Lean_Parser_Module_importPath___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_importPath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Module_importPath___closed__6;
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_Module_importPath___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Module_importPath___elambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_2);
x_15 = l_Lean_Parser_tokenFn(x_2, x_3);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_23 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_22, x_14);
x_6 = x_23;
goto block_13;
}
else
{
lean_dec(x_14);
x_6 = x_15;
goto block_13;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
x_24 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_24, x_14);
x_6 = x_25;
goto block_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_16);
x_26 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_27 = l_Lean_Parser_ParserState_mkErrorsAt(x_15, x_26, x_14);
x_6 = x_27;
goto block_13;
}
block_13:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Parser_Module_importPath___elambda__1(x_1, x_2, x_6);
x_9 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_2);
x_11 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_6, x_11, x_5);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_importPath;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_import___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_import___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import___elambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__3;
x_2 = l_Lean_Parser_Module_import___closed__4;
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
x_1 = l_Lean_Parser_Module_import___closed__5;
return x_1;
}
}
lean_object* l_Lean_Parser_Module_import___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Module_import___elambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
x_8 = l_Lean_Parser_Module_import___elambda__1(x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
if (x_11 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l_Lean_Parser_manyAux___main___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_13);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_7, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_17;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_2);
x_7 = l_Lean_Parser_Module_prelude___elambda__1___rarg(x_2, x_3);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = l_Lean_nullKind;
lean_inc(x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_7, x_9, x_5);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_14, x_1, x_2, x_10);
x_16 = l_Lean_Parser_ParserState_mkNode(x_15, x_9, x_13);
x_17 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_19 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_10, x_19, x_5);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_8);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_21, x_6);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_23 = l_Lean_nullKind;
lean_inc(x_5);
x_24 = l_Lean_Parser_ParserState_mkNode(x_7, x_23, x_5);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_28, x_1, x_2, x_24);
x_30 = l_Lean_Parser_ParserState_mkNode(x_29, x_23, x_27);
x_31 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_dec(x_2);
x_33 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_24, x_33, x_5);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
x_36 = l_Lean_nullKind;
lean_inc(x_5);
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_5);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
x_41 = 0;
x_42 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_41, x_1, x_2, x_37);
x_43 = l_Lean_Parser_ParserState_mkNode(x_42, x_36, x_40);
x_44 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_5);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_38);
lean_dec(x_2);
x_46 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_47 = l_Lean_Parser_ParserState_mkNode(x_37, x_46, x_5);
return x_47;
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
x_7 = l_Lean_mkSearchPathRef___closed__1;
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lean_Parser_commandParserAttribute;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_18 = l_Lean_Parser_ParserAttribute_runParser(x_16, x_17, x_11, x_15);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 0;
lean_ctor_set(x_3, 0, x_22);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
if (x_6 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_Parser_Error_toString(x_26);
x_29 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_11, x_27, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
x_31 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_11, x_27);
x_32 = 1;
lean_ctor_set(x_3, 0, x_31);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_32);
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_19);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_11, x_34);
x_36 = 1;
lean_ctor_set(x_3, 0, x_35);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_36);
goto _start;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_1);
x_39 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_40 = lean_box(0);
x_41 = l_Array_empty___closed__1;
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_40);
x_43 = l_Lean_Parser_commandParserAttribute;
x_44 = lean_unsigned_to_nat(0u);
lean_inc(x_38);
x_45 = l_Lean_Parser_ParserAttribute_runParser(x_43, x_44, x_38, x_42);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = 0;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
if (x_6 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_dec(x_45);
x_56 = l_Lean_Parser_Error_toString(x_54);
x_57 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_38, x_55, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
x_59 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_38, x_55);
x_60 = 1;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_3 = x_61;
x_4 = x_58;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
lean_dec(x_46);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_dec(x_45);
x_64 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_38, x_63);
x_65 = 1;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
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
x_12 = l_Lean_Parser_isEOI(x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Parser_isExitCommand(x_9);
if (x_13 == 0)
{
if (x_3 == 0)
{
lean_dec(x_9);
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(x_9, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_4 = x_10;
x_5 = x_11;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_11);
x_22 = l_List_reverse___rarg(x_11);
x_23 = l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(x_22, x_6);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_26, x_11);
lean_dec(x_11);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; 
x_30 = lean_box(x_26);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = 0;
x_33 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_32, x_11);
lean_dec(x_11);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_11);
x_43 = l_List_reverse___rarg(x_11);
x_44 = l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(x_43, x_6);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = 0;
x_48 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_47, x_11);
lean_dec(x_11);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_44, 0, x_50);
return x_44;
}
else
{
lean_object* x_51; 
x_51 = lean_box(x_47);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
}
else
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = 0;
x_54 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_53, x_11);
lean_dec(x_11);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_55 = 1;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(x_53);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
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
x_2 = lean_alloc_closure((void*)(l_EState_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* lean_test_module_parser(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_testModuleParser___lambda__1___boxed), 7, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_13);
if (x_4 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_16 = l_Lean_Parser_testModuleParser___closed__2;
x_17 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = lean_io_timeit(x_7, x_17, x_5);
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_19, 0, x_11);
x_20 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_15);
x_21 = lean_io_timeit(x_7, x_20, x_5);
lean_dec(x_7);
return x_21;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
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
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_9);
x_3 = x_10;
x_4 = x_11;
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_List_isEmpty___rarg(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = l_List_reverse___rarg(x_11);
x_17 = l_List_forM___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(x_16, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Parser_parseFileAux___main___closed__1;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Parser_parseFileAux___main___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_28 = l_Lean_nullKind;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = l_Lean_Syntax_updateLeading___rarg(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
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
x_16 = l_Lean_mkSearchPathRef___closed__1;
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
l_Lean_Parser_Module_importPath___elambda__1___closed__1 = _init_l_Lean_Parser_Module_importPath___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_importPath___elambda__1___closed__1);
l_Lean_Parser_Module_importPath___elambda__1___closed__2 = _init_l_Lean_Parser_Module_importPath___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_importPath___elambda__1___closed__2);
l_Lean_Parser_Module_importPath___closed__1 = _init_l_Lean_Parser_Module_importPath___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_importPath___closed__1);
l_Lean_Parser_Module_importPath___closed__2 = _init_l_Lean_Parser_Module_importPath___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_importPath___closed__2);
l_Lean_Parser_Module_importPath___closed__3 = _init_l_Lean_Parser_Module_importPath___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_importPath___closed__3);
l_Lean_Parser_Module_importPath___closed__4 = _init_l_Lean_Parser_Module_importPath___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_importPath___closed__4);
l_Lean_Parser_Module_importPath___closed__5 = _init_l_Lean_Parser_Module_importPath___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_importPath___closed__5);
l_Lean_Parser_Module_importPath___closed__6 = _init_l_Lean_Parser_Module_importPath___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_importPath___closed__6);
l_Lean_Parser_Module_importPath = _init_l_Lean_Parser_Module_importPath();
lean_mark_persistent(l_Lean_Parser_Module_importPath);
l_Lean_Parser_Module_import___elambda__1___closed__1 = _init_l_Lean_Parser_Module_import___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__1);
l_Lean_Parser_Module_import___elambda__1___closed__2 = _init_l_Lean_Parser_Module_import___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__2);
l_Lean_Parser_Module_import___elambda__1___closed__3 = _init_l_Lean_Parser_Module_import___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__3);
l_Lean_Parser_Module_import___elambda__1___closed__4 = _init_l_Lean_Parser_Module_import___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__4);
l_Lean_Parser_Module_import___elambda__1___closed__5 = _init_l_Lean_Parser_Module_import___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__5);
l_Lean_Parser_Module_import___elambda__1___closed__6 = _init_l_Lean_Parser_Module_import___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__6);
l_Lean_Parser_Module_import___elambda__1___closed__7 = _init_l_Lean_Parser_Module_import___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__7);
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
