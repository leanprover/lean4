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
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__5;
extern lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserContext(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__8;
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__4;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ModuleParserState_inhabited___closed__1;
lean_object* l_Lean_Parser_testModuleParser___closed__2;
lean_object* l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2;
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1;
lean_object* l_Lean_Parser_Module_prelude;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__12;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__2;
lean_object* l_Lean_Parser_Module_import;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__2;
lean_object* l_Lean_Parser_Module_header___closed__4;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_termIdToAntiquot___closed__3;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_updateTokens___closed__1;
lean_object* l_Lean_Parser_Module_import___closed__9;
lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__3;
lean_object* l_Lean_Parser_parseFile(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__4;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__13;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_2__mkEOI(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__4;
lean_object* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__4;
lean_object* l_Lean_Parser_parseFileAux___main___closed__2;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__11;
extern lean_object* l_Lean_Parser_Command_exit___elambda__1___closed__2;
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseFileAux___main___closed__1;
lean_object* l_Lean_Parser_Module_header___closed__2;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__8;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__1;
lean_object* l_Lean_Parser_whitespace___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_MessageLog_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_IO_print___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___closed__6;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_object* l_Lean_Parser_testModuleParser___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_IO_println___rarg___closed__1;
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__7;
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_Module_import___closed__1;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseFileAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_Inhabited(lean_object*);
lean_object* l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header;
lean_object* l_Lean_Parser_Module_import___closed__6;
lean_object* l_Lean_Parser_Module_header___closed__5;
lean_object* l_Lean_Parser_Module_prelude___closed__5;
lean_object* l_Lean_Parser_Module_import___closed__2;
lean_object* l_Lean_Parser_ModuleParserState_inhabited;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__5;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident___elambda__1(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Substring_drop___closed__2;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__3;
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__3;
lean_object* l_Lean_Parser_Module_prelude___closed__1;
lean_object* l_Lean_Parser_Module_header___closed__7;
lean_object* l_Lean_Parser_Module_import___closed__7;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__6;
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__2;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__7;
lean_object* l_Lean_Parser_Module_header___closed__3;
lean_object* l_String_trim(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_3__consumeInput(lean_object*, lean_object*);
lean_object* lean_io_prim_read_text_file(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__5;
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__3(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__10;
uint8_t l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__3;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__9;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_1__mkErrorMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__8;
lean_object* l_Lean_Parser_parseFileAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__3;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_test_module_parser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__4;
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__6;
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_isEOI___boxed(lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__9;
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Module");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("prelude");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__3;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__5;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__8;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_3 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_123 = lean_ctor_get(x_2, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_2, 1);
lean_inc(x_125);
x_126 = lean_nat_dec_eq(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_123);
lean_inc(x_1);
x_127 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_127;
goto block_122;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_123, 2);
lean_inc(x_128);
lean_dec(x_123);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_129);
x_5 = x_130;
goto block_122;
}
block_122:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Lean_Parser_tokenFn(x_1, x_7);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_17 = lean_string_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_19 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_18, x_10);
x_20 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_22 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_23 = l_Lean_Parser_ParserState_mkNode(x_11, x_22, x_9);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_24 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_25 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_24, x_10);
x_26 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_28 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_29 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_28, x_10);
x_30 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_9);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
if (lean_obj_tag(x_32) == 2)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_36 = lean_string_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_array_get_size(x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
x_40 = l_Lean_Parser_tokenFn(x_1, x_33);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 2)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_48 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_47, x_39);
x_49 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_50 = l_Lean_Parser_ParserState_mkNode(x_48, x_49, x_38);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
x_51 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_52 = l_Lean_Parser_ParserState_mkNode(x_40, x_51, x_38);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
x_53 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_54 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_53, x_39);
x_55 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_56 = l_Lean_Parser_ParserState_mkNode(x_54, x_55, x_38);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
x_57 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_58 = l_Lean_Parser_ParserState_mkErrorsAt(x_40, x_57, x_39);
x_59 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_60 = l_Lean_Parser_ParserState_mkNode(x_58, x_59, x_38);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_33, 0);
lean_inc(x_61);
x_62 = lean_array_get_size(x_61);
lean_dec(x_61);
x_63 = lean_ctor_get(x_33, 1);
lean_inc(x_63);
lean_inc(x_1);
x_64 = lean_apply_2(x_4, x_1, x_33);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_nat_dec_eq(x_67, x_63);
lean_dec(x_67);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc(x_63);
x_69 = l_Lean_Parser_ParserState_restore(x_64, x_62, x_63);
lean_dec(x_62);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_array_get_size(x_70);
lean_dec(x_70);
x_72 = l_Lean_Parser_tokenFn(x_1, x_69);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 2)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_78 = lean_string_dec_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_63);
x_80 = l_Lean_Parser_ParserState_mkErrorsAt(x_72, x_79, x_63);
x_81 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_82 = l_Lean_Parser_ParserState_mkNode(x_80, x_81, x_71);
x_83 = l_Lean_Parser_mergeOrElseErrors(x_82, x_66, x_63);
lean_dec(x_63);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_85 = l_Lean_Parser_ParserState_mkNode(x_72, x_84, x_71);
x_86 = l_Lean_Parser_mergeOrElseErrors(x_85, x_66, x_63);
lean_dec(x_63);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_75);
x_87 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_63);
x_88 = l_Lean_Parser_ParserState_mkErrorsAt(x_72, x_87, x_63);
x_89 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_90 = l_Lean_Parser_ParserState_mkNode(x_88, x_89, x_71);
x_91 = l_Lean_Parser_mergeOrElseErrors(x_90, x_66, x_63);
lean_dec(x_63);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_73);
x_92 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_63);
x_93 = l_Lean_Parser_ParserState_mkErrorsAt(x_72, x_92, x_63);
x_94 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_95 = l_Lean_Parser_ParserState_mkNode(x_93, x_94, x_71);
x_96 = l_Lean_Parser_mergeOrElseErrors(x_95, x_66, x_63);
lean_dec(x_63);
return x_96;
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_32);
lean_dec(x_4);
x_97 = lean_ctor_get(x_5, 0);
lean_inc(x_97);
lean_dec(x_5);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_array_get_size(x_98);
lean_dec(x_98);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
x_101 = l_Lean_Parser_tokenFn(x_1, x_97);
x_102 = lean_ctor_get(x_101, 3);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 2)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_107 = lean_string_dec_eq(x_105, x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_109 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_108, x_100);
x_110 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_111 = l_Lean_Parser_ParserState_mkNode(x_109, x_110, x_99);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_100);
x_112 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_113 = l_Lean_Parser_ParserState_mkNode(x_101, x_112, x_99);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_104);
x_114 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_115 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_114, x_100);
x_116 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_117 = l_Lean_Parser_ParserState_mkNode(x_115, x_116, x_99);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_102);
x_118 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
x_119 = l_Lean_Parser_ParserState_mkErrorsAt(x_101, x_118, x_100);
x_120 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_121 = l_Lean_Parser_ParserState_mkNode(x_119, x_120, x_99);
return x_121;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_2 = l_Lean_Parser_Module_prelude___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_prelude___closed__2;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_prelude___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__3;
x_2 = l_Lean_Parser_Module_prelude___closed__4;
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
x_1 = l_Lean_Parser_Module_prelude___closed__5;
return x_1;
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
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("import ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runtime");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__9;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__12;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___elambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_3 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_434 = lean_ctor_get(x_2, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_2, 1);
lean_inc(x_436);
x_437 = lean_nat_dec_eq(x_435, x_436);
lean_dec(x_436);
lean_dec(x_435);
if (x_437 == 0)
{
lean_object* x_438; 
lean_dec(x_434);
lean_inc(x_1);
x_438 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_438;
goto block_433;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_434, 2);
lean_inc(x_439);
lean_dec(x_434);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_2);
lean_ctor_set(x_441, 1, x_440);
x_5 = x_441;
goto block_433;
}
block_433:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_inc(x_1);
x_62 = l_Lean_Parser_tokenFn(x_1, x_7);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_64);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 2)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_68 = lean_string_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_70 = l_Lean_Parser_ParserState_mkErrorsAt(x_62, x_69, x_61);
x_10 = x_70;
goto block_60;
}
else
{
lean_dec(x_61);
x_10 = x_62;
goto block_60;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
x_71 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_62, x_71, x_61);
x_10 = x_72;
goto block_60;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
x_73 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_74 = l_Lean_Parser_ParserState_mkErrorsAt(x_62, x_73, x_61);
x_10 = x_74;
goto block_60;
}
block_60:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_45; lean_object* x_46; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_1);
x_45 = l_Lean_Parser_tokenFn(x_1, x_10);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 2)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_51 = lean_string_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_14);
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_45, x_52, x_14);
x_15 = x_53;
goto block_44;
}
else
{
x_15 = x_45;
goto block_44;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
x_54 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_14);
x_55 = l_Lean_Parser_ParserState_mkErrorsAt(x_45, x_54, x_14);
x_15 = x_55;
goto block_44;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_46);
x_56 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_14);
x_57 = l_Lean_Parser_ParserState_mkErrorsAt(x_45, x_56, x_14);
x_15 = x_57;
goto block_44;
}
block_44:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_15, x_17, x_13);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Parser_ident___elambda__1(x_1, x_18);
x_21 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_1);
x_23 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_18, x_23, x_9);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_16);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_25, x_14);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_27 = l_Lean_nullKind;
x_28 = l_Lean_Parser_ParserState_mkNode(x_15, x_27, x_13);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Parser_ident___elambda__1(x_1, x_28);
x_31 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_9);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_1);
x_33 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_28, x_33, x_9);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_Parser_ParserState_restore(x_15, x_13, x_14);
x_36 = l_Lean_nullKind;
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_13);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Parser_ident___elambda__1(x_1, x_37);
x_40 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_9);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_1);
x_42 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_43 = l_Lean_Parser_ParserState_mkNode(x_37, x_42, x_9);
return x_43;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
lean_dec(x_1);
x_58 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_59 = l_Lean_Parser_ParserState_mkNode(x_10, x_58, x_9);
return x_59;
}
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_6, 0);
lean_inc(x_75);
lean_dec(x_6);
switch (lean_obj_tag(x_75)) {
case 0:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_4);
x_76 = lean_ctor_get(x_5, 0);
lean_inc(x_76);
lean_dec(x_5);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_array_get_size(x_77);
lean_dec(x_77);
x_130 = lean_ctor_get(x_76, 1);
lean_inc(x_130);
lean_inc(x_1);
x_131 = l_Lean_Parser_tokenFn(x_1, x_76);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_133);
lean_dec(x_133);
if (lean_obj_tag(x_134) == 2)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_137 = lean_string_dec_eq(x_135, x_136);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_139 = l_Lean_Parser_ParserState_mkErrorsAt(x_131, x_138, x_130);
x_79 = x_139;
goto block_129;
}
else
{
lean_dec(x_130);
x_79 = x_131;
goto block_129;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_134);
x_140 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_141 = l_Lean_Parser_ParserState_mkErrorsAt(x_131, x_140, x_130);
x_79 = x_141;
goto block_129;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_132);
x_142 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_143 = l_Lean_Parser_ParserState_mkErrorsAt(x_131, x_142, x_130);
x_79 = x_143;
goto block_129;
}
block_129:
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 3);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_114; lean_object* x_115; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_array_get_size(x_81);
lean_dec(x_81);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_inc(x_1);
x_114 = l_Lean_Parser_tokenFn(x_1, x_79);
x_115 = lean_ctor_get(x_114, 3);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_116);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 2)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_120 = lean_string_dec_eq(x_118, x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_83);
x_122 = l_Lean_Parser_ParserState_mkErrorsAt(x_114, x_121, x_83);
x_84 = x_122;
goto block_113;
}
else
{
x_84 = x_114;
goto block_113;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_117);
x_123 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_83);
x_124 = l_Lean_Parser_ParserState_mkErrorsAt(x_114, x_123, x_83);
x_84 = x_124;
goto block_113;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_115);
x_125 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_83);
x_126 = l_Lean_Parser_ParserState_mkErrorsAt(x_114, x_125, x_83);
x_84 = x_126;
goto block_113;
}
block_113:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 3);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_83);
x_86 = l_Lean_nullKind;
x_87 = l_Lean_Parser_ParserState_mkNode(x_84, x_86, x_82);
x_88 = lean_ctor_get(x_87, 3);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = l_Lean_Parser_ident___elambda__1(x_1, x_87);
x_90 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_91 = l_Lean_Parser_ParserState_mkNode(x_89, x_90, x_78);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_1);
x_92 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_93 = l_Lean_Parser_ParserState_mkNode(x_87, x_92, x_78);
return x_93;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_85);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
x_95 = lean_nat_dec_eq(x_94, x_83);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_83);
x_96 = l_Lean_nullKind;
x_97 = l_Lean_Parser_ParserState_mkNode(x_84, x_96, x_82);
x_98 = lean_ctor_get(x_97, 3);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = l_Lean_Parser_ident___elambda__1(x_1, x_97);
x_100 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_101 = l_Lean_Parser_ParserState_mkNode(x_99, x_100, x_78);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_98);
lean_dec(x_1);
x_102 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_103 = l_Lean_Parser_ParserState_mkNode(x_97, x_102, x_78);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = l_Lean_Parser_ParserState_restore(x_84, x_82, x_83);
x_105 = l_Lean_nullKind;
x_106 = l_Lean_Parser_ParserState_mkNode(x_104, x_105, x_82);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = l_Lean_Parser_ident___elambda__1(x_1, x_106);
x_109 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_110 = l_Lean_Parser_ParserState_mkNode(x_108, x_109, x_78);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
lean_dec(x_1);
x_111 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_112 = l_Lean_Parser_ParserState_mkNode(x_106, x_111, x_78);
return x_112;
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_80);
lean_dec(x_1);
x_127 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_128 = l_Lean_Parser_ParserState_mkNode(x_79, x_127, x_78);
return x_128;
}
}
}
case 1:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_75);
lean_dec(x_4);
x_144 = lean_ctor_get(x_5, 0);
lean_inc(x_144);
lean_dec(x_5);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_array_get_size(x_145);
lean_dec(x_145);
x_198 = lean_ctor_get(x_144, 1);
lean_inc(x_198);
lean_inc(x_1);
x_199 = l_Lean_Parser_tokenFn(x_1, x_144);
x_200 = lean_ctor_get(x_199, 3);
lean_inc(x_200);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_201);
lean_dec(x_201);
if (lean_obj_tag(x_202) == 2)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_205 = lean_string_dec_eq(x_203, x_204);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_207 = l_Lean_Parser_ParserState_mkErrorsAt(x_199, x_206, x_198);
x_147 = x_207;
goto block_197;
}
else
{
lean_dec(x_198);
x_147 = x_199;
goto block_197;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_202);
x_208 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_209 = l_Lean_Parser_ParserState_mkErrorsAt(x_199, x_208, x_198);
x_147 = x_209;
goto block_197;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_200);
x_210 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_211 = l_Lean_Parser_ParserState_mkErrorsAt(x_199, x_210, x_198);
x_147 = x_211;
goto block_197;
}
block_197:
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 3);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_182; lean_object* x_183; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_array_get_size(x_149);
lean_dec(x_149);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_inc(x_1);
x_182 = l_Lean_Parser_tokenFn(x_1, x_147);
x_183 = lean_ctor_get(x_182, 3);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_184);
lean_dec(x_184);
if (lean_obj_tag(x_185) == 2)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_188 = lean_string_dec_eq(x_186, x_187);
lean_dec(x_186);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_151);
x_190 = l_Lean_Parser_ParserState_mkErrorsAt(x_182, x_189, x_151);
x_152 = x_190;
goto block_181;
}
else
{
x_152 = x_182;
goto block_181;
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_185);
x_191 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_151);
x_192 = l_Lean_Parser_ParserState_mkErrorsAt(x_182, x_191, x_151);
x_152 = x_192;
goto block_181;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_183);
x_193 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_151);
x_194 = l_Lean_Parser_ParserState_mkErrorsAt(x_182, x_193, x_151);
x_152 = x_194;
goto block_181;
}
block_181:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 3);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_151);
x_154 = l_Lean_nullKind;
x_155 = l_Lean_Parser_ParserState_mkNode(x_152, x_154, x_150);
x_156 = lean_ctor_get(x_155, 3);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = l_Lean_Parser_ident___elambda__1(x_1, x_155);
x_158 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_159 = l_Lean_Parser_ParserState_mkNode(x_157, x_158, x_146);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_156);
lean_dec(x_1);
x_160 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_161 = l_Lean_Parser_ParserState_mkNode(x_155, x_160, x_146);
return x_161;
}
}
else
{
lean_object* x_162; uint8_t x_163; 
lean_dec(x_153);
x_162 = lean_ctor_get(x_152, 1);
lean_inc(x_162);
x_163 = lean_nat_dec_eq(x_162, x_151);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_151);
x_164 = l_Lean_nullKind;
x_165 = l_Lean_Parser_ParserState_mkNode(x_152, x_164, x_150);
x_166 = lean_ctor_get(x_165, 3);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = l_Lean_Parser_ident___elambda__1(x_1, x_165);
x_168 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_169 = l_Lean_Parser_ParserState_mkNode(x_167, x_168, x_146);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_166);
lean_dec(x_1);
x_170 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_171 = l_Lean_Parser_ParserState_mkNode(x_165, x_170, x_146);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = l_Lean_Parser_ParserState_restore(x_152, x_150, x_151);
x_173 = l_Lean_nullKind;
x_174 = l_Lean_Parser_ParserState_mkNode(x_172, x_173, x_150);
x_175 = lean_ctor_get(x_174, 3);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = l_Lean_Parser_ident___elambda__1(x_1, x_174);
x_177 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_178 = l_Lean_Parser_ParserState_mkNode(x_176, x_177, x_146);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_175);
lean_dec(x_1);
x_179 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_180 = l_Lean_Parser_ParserState_mkNode(x_174, x_179, x_146);
return x_180;
}
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_148);
lean_dec(x_1);
x_195 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_196 = l_Lean_Parser_ParserState_mkNode(x_147, x_195, x_146);
return x_196;
}
}
}
case 2:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_212 = lean_ctor_get(x_5, 0);
lean_inc(x_212);
lean_dec(x_5);
x_213 = lean_ctor_get(x_75, 1);
lean_inc(x_213);
lean_dec(x_75);
x_214 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_215 = lean_string_dec_eq(x_213, x_214);
lean_dec(x_213);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_4);
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
x_217 = lean_array_get_size(x_216);
lean_dec(x_216);
x_269 = lean_ctor_get(x_212, 1);
lean_inc(x_269);
lean_inc(x_1);
x_270 = l_Lean_Parser_tokenFn(x_1, x_212);
x_271 = lean_ctor_get(x_270, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
x_273 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_272);
lean_dec(x_272);
if (lean_obj_tag(x_273) == 2)
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_275 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_276 = lean_string_dec_eq(x_274, x_275);
lean_dec(x_274);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_278 = l_Lean_Parser_ParserState_mkErrorsAt(x_270, x_277, x_269);
x_218 = x_278;
goto block_268;
}
else
{
lean_dec(x_269);
x_218 = x_270;
goto block_268;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_273);
x_279 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_280 = l_Lean_Parser_ParserState_mkErrorsAt(x_270, x_279, x_269);
x_218 = x_280;
goto block_268;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_271);
x_281 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_282 = l_Lean_Parser_ParserState_mkErrorsAt(x_270, x_281, x_269);
x_218 = x_282;
goto block_268;
}
block_268:
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 3);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_253; lean_object* x_254; 
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_array_get_size(x_220);
lean_dec(x_220);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_inc(x_1);
x_253 = l_Lean_Parser_tokenFn(x_1, x_218);
x_254 = lean_ctor_get(x_253, 3);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_255);
lean_dec(x_255);
if (lean_obj_tag(x_256) == 2)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_259 = lean_string_dec_eq(x_257, x_258);
lean_dec(x_257);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_222);
x_261 = l_Lean_Parser_ParserState_mkErrorsAt(x_253, x_260, x_222);
x_223 = x_261;
goto block_252;
}
else
{
x_223 = x_253;
goto block_252;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_256);
x_262 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_222);
x_263 = l_Lean_Parser_ParserState_mkErrorsAt(x_253, x_262, x_222);
x_223 = x_263;
goto block_252;
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_254);
x_264 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_222);
x_265 = l_Lean_Parser_ParserState_mkErrorsAt(x_253, x_264, x_222);
x_223 = x_265;
goto block_252;
}
block_252:
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 3);
lean_inc(x_224);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_222);
x_225 = l_Lean_nullKind;
x_226 = l_Lean_Parser_ParserState_mkNode(x_223, x_225, x_221);
x_227 = lean_ctor_get(x_226, 3);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = l_Lean_Parser_ident___elambda__1(x_1, x_226);
x_229 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_230 = l_Lean_Parser_ParserState_mkNode(x_228, x_229, x_217);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_227);
lean_dec(x_1);
x_231 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_232 = l_Lean_Parser_ParserState_mkNode(x_226, x_231, x_217);
return x_232;
}
}
else
{
lean_object* x_233; uint8_t x_234; 
lean_dec(x_224);
x_233 = lean_ctor_get(x_223, 1);
lean_inc(x_233);
x_234 = lean_nat_dec_eq(x_233, x_222);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_222);
x_235 = l_Lean_nullKind;
x_236 = l_Lean_Parser_ParserState_mkNode(x_223, x_235, x_221);
x_237 = lean_ctor_get(x_236, 3);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = l_Lean_Parser_ident___elambda__1(x_1, x_236);
x_239 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_240 = l_Lean_Parser_ParserState_mkNode(x_238, x_239, x_217);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_237);
lean_dec(x_1);
x_241 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_242 = l_Lean_Parser_ParserState_mkNode(x_236, x_241, x_217);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = l_Lean_Parser_ParserState_restore(x_223, x_221, x_222);
x_244 = l_Lean_nullKind;
x_245 = l_Lean_Parser_ParserState_mkNode(x_243, x_244, x_221);
x_246 = lean_ctor_get(x_245, 3);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = l_Lean_Parser_ident___elambda__1(x_1, x_245);
x_248 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_249 = l_Lean_Parser_ParserState_mkNode(x_247, x_248, x_217);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_246);
lean_dec(x_1);
x_250 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_251 = l_Lean_Parser_ParserState_mkNode(x_245, x_250, x_217);
return x_251;
}
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_219);
lean_dec(x_1);
x_266 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_267 = l_Lean_Parser_ParserState_mkNode(x_218, x_266, x_217);
return x_267;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_212, 0);
lean_inc(x_283);
x_284 = lean_array_get_size(x_283);
lean_dec(x_283);
x_285 = lean_ctor_get(x_212, 1);
lean_inc(x_285);
lean_inc(x_1);
x_286 = lean_apply_2(x_4, x_1, x_212);
x_287 = lean_ctor_get(x_286, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_1);
return x_286;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec(x_287);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
x_290 = lean_nat_dec_eq(x_289, x_285);
lean_dec(x_289);
if (x_290 == 0)
{
lean_dec(x_288);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_1);
return x_286;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_352; lean_object* x_353; 
lean_inc(x_285);
x_291 = l_Lean_Parser_ParserState_restore(x_286, x_284, x_285);
lean_dec(x_284);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_array_get_size(x_292);
lean_dec(x_292);
lean_inc(x_1);
x_352 = l_Lean_Parser_tokenFn(x_1, x_291);
x_353 = lean_ctor_get(x_352, 3);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_354);
lean_dec(x_354);
if (lean_obj_tag(x_355) == 2)
{
lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
x_357 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_358 = lean_string_dec_eq(x_356, x_357);
lean_dec(x_356);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_285);
x_360 = l_Lean_Parser_ParserState_mkErrorsAt(x_352, x_359, x_285);
x_294 = x_360;
goto block_351;
}
else
{
x_294 = x_352;
goto block_351;
}
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_355);
x_361 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_285);
x_362 = l_Lean_Parser_ParserState_mkErrorsAt(x_352, x_361, x_285);
x_294 = x_362;
goto block_351;
}
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_353);
x_363 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_285);
x_364 = l_Lean_Parser_ParserState_mkErrorsAt(x_352, x_363, x_285);
x_294 = x_364;
goto block_351;
}
block_351:
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 3);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_335; lean_object* x_336; 
x_296 = lean_ctor_get(x_294, 0);
lean_inc(x_296);
x_297 = lean_array_get_size(x_296);
lean_dec(x_296);
x_298 = lean_ctor_get(x_294, 1);
lean_inc(x_298);
lean_inc(x_1);
x_335 = l_Lean_Parser_tokenFn(x_1, x_294);
x_336 = lean_ctor_get(x_335, 3);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
x_338 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_337);
lean_dec(x_337);
if (lean_obj_tag(x_338) == 2)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_341 = lean_string_dec_eq(x_339, x_340);
lean_dec(x_339);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_298);
x_343 = l_Lean_Parser_ParserState_mkErrorsAt(x_335, x_342, x_298);
x_299 = x_343;
goto block_334;
}
else
{
x_299 = x_335;
goto block_334;
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_338);
x_344 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_298);
x_345 = l_Lean_Parser_ParserState_mkErrorsAt(x_335, x_344, x_298);
x_299 = x_345;
goto block_334;
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_336);
x_346 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_298);
x_347 = l_Lean_Parser_ParserState_mkErrorsAt(x_335, x_346, x_298);
x_299 = x_347;
goto block_334;
}
block_334:
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 3);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_298);
x_301 = l_Lean_nullKind;
x_302 = l_Lean_Parser_ParserState_mkNode(x_299, x_301, x_297);
x_303 = lean_ctor_get(x_302, 3);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = l_Lean_Parser_ident___elambda__1(x_1, x_302);
x_305 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_306 = l_Lean_Parser_ParserState_mkNode(x_304, x_305, x_293);
x_307 = l_Lean_Parser_mergeOrElseErrors(x_306, x_288, x_285);
lean_dec(x_285);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_303);
lean_dec(x_1);
x_308 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_309 = l_Lean_Parser_ParserState_mkNode(x_302, x_308, x_293);
x_310 = l_Lean_Parser_mergeOrElseErrors(x_309, x_288, x_285);
lean_dec(x_285);
return x_310;
}
}
else
{
lean_object* x_311; uint8_t x_312; 
lean_dec(x_300);
x_311 = lean_ctor_get(x_299, 1);
lean_inc(x_311);
x_312 = lean_nat_dec_eq(x_311, x_298);
lean_dec(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_298);
x_313 = l_Lean_nullKind;
x_314 = l_Lean_Parser_ParserState_mkNode(x_299, x_313, x_297);
x_315 = lean_ctor_get(x_314, 3);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = l_Lean_Parser_ident___elambda__1(x_1, x_314);
x_317 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_318 = l_Lean_Parser_ParserState_mkNode(x_316, x_317, x_293);
x_319 = l_Lean_Parser_mergeOrElseErrors(x_318, x_288, x_285);
lean_dec(x_285);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_315);
lean_dec(x_1);
x_320 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_321 = l_Lean_Parser_ParserState_mkNode(x_314, x_320, x_293);
x_322 = l_Lean_Parser_mergeOrElseErrors(x_321, x_288, x_285);
lean_dec(x_285);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_323 = l_Lean_Parser_ParserState_restore(x_299, x_297, x_298);
x_324 = l_Lean_nullKind;
x_325 = l_Lean_Parser_ParserState_mkNode(x_323, x_324, x_297);
x_326 = lean_ctor_get(x_325, 3);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = l_Lean_Parser_ident___elambda__1(x_1, x_325);
x_328 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_329 = l_Lean_Parser_ParserState_mkNode(x_327, x_328, x_293);
x_330 = l_Lean_Parser_mergeOrElseErrors(x_329, x_288, x_285);
lean_dec(x_285);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_326);
lean_dec(x_1);
x_331 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_332 = l_Lean_Parser_ParserState_mkNode(x_325, x_331, x_293);
x_333 = l_Lean_Parser_mergeOrElseErrors(x_332, x_288, x_285);
lean_dec(x_285);
return x_333;
}
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_295);
lean_dec(x_1);
x_348 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_349 = l_Lean_Parser_ParserState_mkNode(x_294, x_348, x_293);
x_350 = l_Lean_Parser_mergeOrElseErrors(x_349, x_288, x_285);
lean_dec(x_285);
return x_350;
}
}
}
}
}
}
default: 
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_75);
lean_dec(x_4);
x_365 = lean_ctor_get(x_5, 0);
lean_inc(x_365);
lean_dec(x_5);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_array_get_size(x_366);
lean_dec(x_366);
x_419 = lean_ctor_get(x_365, 1);
lean_inc(x_419);
lean_inc(x_1);
x_420 = l_Lean_Parser_tokenFn(x_1, x_365);
x_421 = lean_ctor_get(x_420, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_422);
lean_dec(x_422);
if (lean_obj_tag(x_423) == 2)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_426 = lean_string_dec_eq(x_424, x_425);
lean_dec(x_424);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_428 = l_Lean_Parser_ParserState_mkErrorsAt(x_420, x_427, x_419);
x_368 = x_428;
goto block_418;
}
else
{
lean_dec(x_419);
x_368 = x_420;
goto block_418;
}
}
else
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_423);
x_429 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_430 = l_Lean_Parser_ParserState_mkErrorsAt(x_420, x_429, x_419);
x_368 = x_430;
goto block_418;
}
}
else
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_421);
x_431 = l_Lean_Parser_Module_import___elambda__1___closed__14;
x_432 = l_Lean_Parser_ParserState_mkErrorsAt(x_420, x_431, x_419);
x_368 = x_432;
goto block_418;
}
block_418:
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_368, 3);
lean_inc(x_369);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_403; lean_object* x_404; 
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_array_get_size(x_370);
lean_dec(x_370);
x_372 = lean_ctor_get(x_368, 1);
lean_inc(x_372);
lean_inc(x_1);
x_403 = l_Lean_Parser_tokenFn(x_1, x_368);
x_404 = lean_ctor_get(x_403, 3);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_403, 0);
lean_inc(x_405);
x_406 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_405);
lean_dec(x_405);
if (lean_obj_tag(x_406) == 2)
{
lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
x_408 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_409 = lean_string_dec_eq(x_407, x_408);
lean_dec(x_407);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_372);
x_411 = l_Lean_Parser_ParserState_mkErrorsAt(x_403, x_410, x_372);
x_373 = x_411;
goto block_402;
}
else
{
x_373 = x_403;
goto block_402;
}
}
else
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_406);
x_412 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_372);
x_413 = l_Lean_Parser_ParserState_mkErrorsAt(x_403, x_412, x_372);
x_373 = x_413;
goto block_402;
}
}
else
{
lean_object* x_414; lean_object* x_415; 
lean_dec(x_404);
x_414 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_372);
x_415 = l_Lean_Parser_ParserState_mkErrorsAt(x_403, x_414, x_372);
x_373 = x_415;
goto block_402;
}
block_402:
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_373, 3);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_372);
x_375 = l_Lean_nullKind;
x_376 = l_Lean_Parser_ParserState_mkNode(x_373, x_375, x_371);
x_377 = lean_ctor_get(x_376, 3);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = l_Lean_Parser_ident___elambda__1(x_1, x_376);
x_379 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_380 = l_Lean_Parser_ParserState_mkNode(x_378, x_379, x_367);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; 
lean_dec(x_377);
lean_dec(x_1);
x_381 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_382 = l_Lean_Parser_ParserState_mkNode(x_376, x_381, x_367);
return x_382;
}
}
else
{
lean_object* x_383; uint8_t x_384; 
lean_dec(x_374);
x_383 = lean_ctor_get(x_373, 1);
lean_inc(x_383);
x_384 = lean_nat_dec_eq(x_383, x_372);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_372);
x_385 = l_Lean_nullKind;
x_386 = l_Lean_Parser_ParserState_mkNode(x_373, x_385, x_371);
x_387 = lean_ctor_get(x_386, 3);
lean_inc(x_387);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = l_Lean_Parser_ident___elambda__1(x_1, x_386);
x_389 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_390 = l_Lean_Parser_ParserState_mkNode(x_388, x_389, x_367);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_387);
lean_dec(x_1);
x_391 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_392 = l_Lean_Parser_ParserState_mkNode(x_386, x_391, x_367);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = l_Lean_Parser_ParserState_restore(x_373, x_371, x_372);
x_394 = l_Lean_nullKind;
x_395 = l_Lean_Parser_ParserState_mkNode(x_393, x_394, x_371);
x_396 = lean_ctor_get(x_395, 3);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = l_Lean_Parser_ident___elambda__1(x_1, x_395);
x_398 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_399 = l_Lean_Parser_ParserState_mkNode(x_397, x_398, x_367);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_396);
lean_dec(x_1);
x_400 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_401 = l_Lean_Parser_ParserState_mkNode(x_395, x_400, x_367);
return x_401;
}
}
}
}
}
else
{
lean_object* x_416; lean_object* x_417; 
lean_dec(x_369);
lean_dec(x_1);
x_416 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_417 = l_Lean_Parser_ParserState_mkNode(x_368, x_416, x_367);
return x_417;
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__8;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_import___closed__3;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
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
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_import___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_import___closed__6;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_import___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__7;
x_2 = l_Lean_Parser_Module_import___closed__8;
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
x_1 = l_Lean_Parser_Module_import___closed__9;
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_Parser_Module_import___elambda__1(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Parser_manyAux___main___closed__1;
x_12 = l_Lean_Parser_ParserState_mkUnexpectedError(x_6, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_5, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
return x_15;
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
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Module_header___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__4;
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_193 = lean_ctor_get(x_2, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_2, 1);
lean_inc(x_195);
x_196 = lean_nat_dec_eq(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_193);
lean_inc(x_1);
x_197 = l_Lean_Parser_peekTokenAux(x_1, x_2);
x_5 = x_197;
goto block_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_193, 2);
lean_inc(x_198);
lean_dec(x_193);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_2);
lean_ctor_set(x_200, 1, x_199);
x_5 = x_200;
goto block_192;
}
block_192:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_Parser_Module_prelude___elambda__1(x_1, x_7);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = l_Lean_nullKind;
lean_inc(x_9);
x_14 = l_Lean_Parser_ParserState_mkNode(x_11, x_13, x_9);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_14);
x_19 = l_Lean_Parser_ParserState_mkNode(x_18, x_13, x_17);
x_20 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_1);
x_22 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_14, x_22, x_9);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_24, x_10);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_26 = l_Lean_nullKind;
lean_inc(x_9);
x_27 = l_Lean_Parser_ParserState_mkNode(x_11, x_26, x_9);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_27);
x_32 = l_Lean_Parser_ParserState_mkNode(x_31, x_26, x_30);
x_33 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_32, x_33, x_9);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_1);
x_35 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_27, x_35, x_9);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
x_38 = l_Lean_nullKind;
lean_inc(x_9);
x_39 = l_Lean_Parser_ParserState_mkNode(x_37, x_38, x_9);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_array_get_size(x_41);
lean_dec(x_41);
x_43 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_39);
x_44 = l_Lean_Parser_ParserState_mkNode(x_43, x_38, x_42);
x_45 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_9);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_1);
x_47 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_39, x_47, x_9);
return x_48;
}
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_6, 0);
lean_inc(x_49);
lean_dec(x_6);
if (lean_obj_tag(x_49) == 2)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_5, 0);
lean_inc(x_50);
lean_dec(x_5);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_53 = lean_string_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_1);
x_57 = l_Lean_Parser_Module_prelude___elambda__1(x_1, x_50);
x_58 = lean_ctor_get(x_57, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_56);
x_59 = l_Lean_nullKind;
lean_inc(x_55);
x_60 = l_Lean_Parser_ParserState_mkNode(x_57, x_59, x_55);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
x_64 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_60);
x_65 = l_Lean_Parser_ParserState_mkNode(x_64, x_59, x_63);
x_66 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_67 = l_Lean_Parser_ParserState_mkNode(x_65, x_66, x_55);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_61);
lean_dec(x_1);
x_68 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_69 = l_Lean_Parser_ParserState_mkNode(x_60, x_68, x_55);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_58);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
x_71 = lean_nat_dec_eq(x_70, x_56);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_56);
x_72 = l_Lean_nullKind;
lean_inc(x_55);
x_73 = l_Lean_Parser_ParserState_mkNode(x_57, x_72, x_55);
x_74 = lean_ctor_get(x_73, 3);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_array_get_size(x_75);
lean_dec(x_75);
x_77 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_73);
x_78 = l_Lean_Parser_ParserState_mkNode(x_77, x_72, x_76);
x_79 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_80 = l_Lean_Parser_ParserState_mkNode(x_78, x_79, x_55);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
lean_dec(x_1);
x_81 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_82 = l_Lean_Parser_ParserState_mkNode(x_73, x_81, x_55);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = l_Lean_Parser_ParserState_restore(x_57, x_55, x_56);
x_84 = l_Lean_nullKind;
lean_inc(x_55);
x_85 = l_Lean_Parser_ParserState_mkNode(x_83, x_84, x_55);
x_86 = lean_ctor_get(x_85, 3);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_array_get_size(x_87);
lean_dec(x_87);
x_89 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_85);
x_90 = l_Lean_Parser_ParserState_mkNode(x_89, x_84, x_88);
x_91 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_92 = l_Lean_Parser_ParserState_mkNode(x_90, x_91, x_55);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_86);
lean_dec(x_1);
x_93 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_94 = l_Lean_Parser_ParserState_mkNode(x_85, x_93, x_55);
return x_94;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_50, 0);
lean_inc(x_95);
x_96 = lean_array_get_size(x_95);
lean_dec(x_95);
x_97 = lean_ctor_get(x_50, 1);
lean_inc(x_97);
lean_inc(x_1);
x_98 = lean_apply_2(x_4, x_1, x_50);
x_99 = lean_ctor_get(x_98, 3);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
x_102 = lean_nat_dec_eq(x_101, x_97);
lean_dec(x_101);
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_1);
return x_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_inc(x_97);
x_103 = l_Lean_Parser_ParserState_restore(x_98, x_96, x_97);
lean_dec(x_96);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_array_get_size(x_104);
lean_dec(x_104);
lean_inc(x_1);
x_106 = l_Lean_Parser_Module_prelude___elambda__1(x_1, x_103);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = l_Lean_nullKind;
lean_inc(x_105);
x_109 = l_Lean_Parser_ParserState_mkNode(x_106, x_108, x_105);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_array_get_size(x_111);
lean_dec(x_111);
x_113 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_109);
x_114 = l_Lean_Parser_ParserState_mkNode(x_113, x_108, x_112);
x_115 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_116 = l_Lean_Parser_ParserState_mkNode(x_114, x_115, x_105);
x_117 = l_Lean_Parser_mergeOrElseErrors(x_116, x_100, x_97);
lean_dec(x_97);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_110);
lean_dec(x_1);
x_118 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_119 = l_Lean_Parser_ParserState_mkNode(x_109, x_118, x_105);
x_120 = l_Lean_Parser_mergeOrElseErrors(x_119, x_100, x_97);
lean_dec(x_97);
return x_120;
}
}
else
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_107);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
x_122 = lean_nat_dec_eq(x_121, x_97);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = l_Lean_nullKind;
lean_inc(x_105);
x_124 = l_Lean_Parser_ParserState_mkNode(x_106, x_123, x_105);
x_125 = lean_ctor_get(x_124, 3);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_array_get_size(x_126);
lean_dec(x_126);
x_128 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_124);
x_129 = l_Lean_Parser_ParserState_mkNode(x_128, x_123, x_127);
x_130 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_131 = l_Lean_Parser_ParserState_mkNode(x_129, x_130, x_105);
x_132 = l_Lean_Parser_mergeOrElseErrors(x_131, x_100, x_97);
lean_dec(x_97);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
lean_dec(x_1);
x_133 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_134 = l_Lean_Parser_ParserState_mkNode(x_124, x_133, x_105);
x_135 = l_Lean_Parser_mergeOrElseErrors(x_134, x_100, x_97);
lean_dec(x_97);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_inc(x_97);
x_136 = l_Lean_Parser_ParserState_restore(x_106, x_105, x_97);
x_137 = l_Lean_nullKind;
lean_inc(x_105);
x_138 = l_Lean_Parser_ParserState_mkNode(x_136, x_137, x_105);
x_139 = lean_ctor_get(x_138, 3);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_array_get_size(x_140);
lean_dec(x_140);
x_142 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_138);
x_143 = l_Lean_Parser_ParserState_mkNode(x_142, x_137, x_141);
x_144 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_145 = l_Lean_Parser_ParserState_mkNode(x_143, x_144, x_105);
x_146 = l_Lean_Parser_mergeOrElseErrors(x_145, x_100, x_97);
lean_dec(x_97);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_139);
lean_dec(x_1);
x_147 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_148 = l_Lean_Parser_ParserState_mkNode(x_138, x_147, x_105);
x_149 = l_Lean_Parser_mergeOrElseErrors(x_148, x_100, x_97);
lean_dec(x_97);
return x_149;
}
}
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_49);
lean_dec(x_4);
x_150 = lean_ctor_get(x_5, 0);
lean_inc(x_150);
lean_dec(x_5);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_array_get_size(x_151);
lean_dec(x_151);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_inc(x_1);
x_154 = l_Lean_Parser_Module_prelude___elambda__1(x_1, x_150);
x_155 = lean_ctor_get(x_154, 3);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_153);
x_156 = l_Lean_nullKind;
lean_inc(x_152);
x_157 = l_Lean_Parser_ParserState_mkNode(x_154, x_156, x_152);
x_158 = lean_ctor_get(x_157, 3);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_array_get_size(x_159);
lean_dec(x_159);
x_161 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_157);
x_162 = l_Lean_Parser_ParserState_mkNode(x_161, x_156, x_160);
x_163 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_164 = l_Lean_Parser_ParserState_mkNode(x_162, x_163, x_152);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_1);
x_165 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_166 = l_Lean_Parser_ParserState_mkNode(x_157, x_165, x_152);
return x_166;
}
}
else
{
lean_object* x_167; uint8_t x_168; 
lean_dec(x_155);
x_167 = lean_ctor_get(x_154, 1);
lean_inc(x_167);
x_168 = lean_nat_dec_eq(x_167, x_153);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_153);
x_169 = l_Lean_nullKind;
lean_inc(x_152);
x_170 = l_Lean_Parser_ParserState_mkNode(x_154, x_169, x_152);
x_171 = lean_ctor_get(x_170, 3);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_array_get_size(x_172);
lean_dec(x_172);
x_174 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_170);
x_175 = l_Lean_Parser_ParserState_mkNode(x_174, x_169, x_173);
x_176 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_177 = l_Lean_Parser_ParserState_mkNode(x_175, x_176, x_152);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_171);
lean_dec(x_1);
x_178 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_179 = l_Lean_Parser_ParserState_mkNode(x_170, x_178, x_152);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = l_Lean_Parser_ParserState_restore(x_154, x_152, x_153);
x_181 = l_Lean_nullKind;
lean_inc(x_152);
x_182 = l_Lean_Parser_ParserState_mkNode(x_180, x_181, x_152);
x_183 = lean_ctor_get(x_182, 3);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_array_get_size(x_184);
lean_dec(x_184);
x_186 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_1, x_182);
x_187 = l_Lean_Parser_ParserState_mkNode(x_186, x_181, x_185);
x_188 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_189 = l_Lean_Parser_ParserState_mkNode(x_187, x_188, x_152);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_183);
lean_dec(x_1);
x_190 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_191 = l_Lean_Parser_ParserState_mkNode(x_182, x_190, x_152);
return x_191;
}
}
}
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_Module_header___closed__4;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header___elambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_header___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__5;
x_2 = l_Lean_Parser_Module_header___closed__6;
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
x_1 = l_Lean_Parser_Module_header___closed__7;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Module_updateTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Trie_Inhabited(lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Parser_Module_updateTokens(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_Parser_Module_header;
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_addParserTokens(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = l_Lean_Parser_Module_updateTokens___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
lean_ctor_set(x_1, 3, x_8);
return x_1;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_1, 3, x_9);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_14 = l_Lean_Parser_Module_header;
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_Parser_addParserTokens(x_13, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_17 = l_Lean_Parser_Module_updateTokens___closed__1;
x_18 = l_unreachable_x21___rarg(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_12);
lean_ctor_set(x_21, 3, x_20);
return x_21;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_Parser_mkParserContext(x_1, x_2);
x_4 = l_Lean_Parser_Module_updateTokens(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Parser_mkParserState(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_whitespace___main(x_4, x_7);
lean_inc(x_4);
x_9 = l_Lean_Parser_Module_header___elambda__1(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = l_PersistentArray_empty___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lean_Parser_Error_toString(x_19);
x_22 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_4, x_20, x_21);
lean_dec(x_4);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = l_PersistentArray_empty___closed__3;
x_26 = l_PersistentArray_push___rarg(x_25, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
x_1 = l_Lean_Parser_Module_prelude___elambda__1___closed__2;
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
x_7 = l_Lean_mkOptionalNode___closed__2;
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
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_isEOI___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isEOI(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Parser_isExitCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Command_exit___elambda__1___closed__2;
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isExitCommand(x_1);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Parser_mkParserContext(x_1, x_2);
x_12 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lean_Parser_whitespace___main(x_11, x_15);
x_17 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_19 = l_Lean_Parser_categoryParser___elambda__1(x_17, x_18, x_11, x_16);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 0;
lean_ctor_set(x_3, 0, x_23);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
if (x_6 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Parser_Error_toString(x_27);
x_30 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_11, x_28, x_29);
x_31 = l_PersistentArray_push___rarg(x_4, x_30);
x_32 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_11, x_28);
x_33 = 1;
lean_ctor_set(x_3, 0, x_32);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_33);
x_4 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_20);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_11, x_35);
x_37 = 1;
lean_ctor_set(x_3, 0, x_36);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_37);
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_Parser_mkParserContext(x_1, x_2);
x_40 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = l_Array_empty___closed__1;
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = l_Lean_Parser_whitespace___main(x_39, x_43);
x_45 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
x_46 = lean_unsigned_to_nat(0u);
lean_inc(x_39);
x_47 = l_Lean_Parser_categoryParser___elambda__1(x_45, x_46, x_39, x_44);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = 0;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
if (x_6 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = l_Lean_Parser_Error_toString(x_56);
x_59 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_39, x_57, x_58);
x_60 = l_PersistentArray_push___rarg(x_4, x_59);
x_61 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_39, x_57);
x_62 = 1;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_3 = x_63;
x_4 = x_60;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
lean_dec(x_48);
x_65 = lean_ctor_get(x_47, 1);
lean_inc(x_65);
lean_dec(x_47);
x_66 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_39, x_65);
x_67 = 1;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_3 = x_68;
goto _start;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_70 = l___private_Init_Lean_Parser_Module_2__mkEOI(x_5);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_4);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux___main(x_3, x_4, x_1);
x_6 = l_Lean_Options_empty;
x_7 = l_Lean_Format_pretty(x_5, x_6);
x_8 = lean_io_prim_put_str(x_7, x_2);
lean_dec(x_7);
return x_8;
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
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_10 = l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7(x_1, x_9, x_4);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8(x_1, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9(x_1, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7(x_1, x_4, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__10(x_1, x_5, x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_MessageLog_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_2, x_1, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__3), 2, 0);
return x_1;
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
lean_inc(x_9);
x_12 = l_Lean_Parser_isEOI(x_9);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_9);
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
x_22 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
x_23 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_22, x_11, x_6);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
uint8_t x_29; lean_object* x_30; 
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_box(x_36);
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
x_43 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
x_44 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_43, x_11, x_6);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; 
x_48 = 1;
x_49 = lean_box(x_48);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
uint8_t x_50; lean_object* x_51; 
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_box(x_57);
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
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_MessageLog_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageLog_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = l_Lean_Parser_testModuleParser___closed__1;
lean_inc(x_3);
x_7 = lean_string_append(x_3, x_6);
x_8 = l_Lean_Parser_mkInputContext(x_2, x_3);
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
x_17 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
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
x_20 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
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
lean_object* _init_l_Lean_Parser_parseFileAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_parseFileAux___main___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_inc(x_9);
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
x_15 = l_PersistentArray_isEmpty___rarg(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
x_17 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_16, x_11, x_6);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Parser_parseFileAux___main___closed__2;
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
x_22 = l_Lean_Parser_parseFileAux___main___closed__2;
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
x_30 = l_Lean_Syntax_updateLeading(x_29);
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
x_10 = l_Lean_Parser_mkInputContext(x_8, x_5);
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
x_16 = l_Lean_mkOptionalNode___closed__2;
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
l_Lean_Parser_Module_prelude___elambda__1___closed__1 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__1);
l_Lean_Parser_Module_prelude___elambda__1___closed__2 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__2);
l_Lean_Parser_Module_prelude___elambda__1___closed__3 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__3);
l_Lean_Parser_Module_prelude___elambda__1___closed__4 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__4);
l_Lean_Parser_Module_prelude___elambda__1___closed__5 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__5);
l_Lean_Parser_Module_prelude___elambda__1___closed__6 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__6);
l_Lean_Parser_Module_prelude___elambda__1___closed__7 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__7);
l_Lean_Parser_Module_prelude___elambda__1___closed__8 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__8);
l_Lean_Parser_Module_prelude___elambda__1___closed__9 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__9);
l_Lean_Parser_Module_prelude___elambda__1___closed__10 = _init_l_Lean_Parser_Module_prelude___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___closed__10);
l_Lean_Parser_Module_prelude___closed__1 = _init_l_Lean_Parser_Module_prelude___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__1);
l_Lean_Parser_Module_prelude___closed__2 = _init_l_Lean_Parser_Module_prelude___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__2);
l_Lean_Parser_Module_prelude___closed__3 = _init_l_Lean_Parser_Module_prelude___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__3);
l_Lean_Parser_Module_prelude___closed__4 = _init_l_Lean_Parser_Module_prelude___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__4);
l_Lean_Parser_Module_prelude___closed__5 = _init_l_Lean_Parser_Module_prelude___closed__5();
lean_mark_persistent(l_Lean_Parser_Module_prelude___closed__5);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
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
l_Lean_Parser_Module_import___elambda__1___closed__8 = _init_l_Lean_Parser_Module_import___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__8);
l_Lean_Parser_Module_import___elambda__1___closed__9 = _init_l_Lean_Parser_Module_import___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__9);
l_Lean_Parser_Module_import___elambda__1___closed__10 = _init_l_Lean_Parser_Module_import___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__10);
l_Lean_Parser_Module_import___elambda__1___closed__11 = _init_l_Lean_Parser_Module_import___elambda__1___closed__11();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__11);
l_Lean_Parser_Module_import___elambda__1___closed__12 = _init_l_Lean_Parser_Module_import___elambda__1___closed__12();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__12);
l_Lean_Parser_Module_import___elambda__1___closed__13 = _init_l_Lean_Parser_Module_import___elambda__1___closed__13();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__13);
l_Lean_Parser_Module_import___elambda__1___closed__14 = _init_l_Lean_Parser_Module_import___elambda__1___closed__14();
lean_mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__14);
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
l_Lean_Parser_Module_import___closed__9 = _init_l_Lean_Parser_Module_import___closed__9();
lean_mark_persistent(l_Lean_Parser_Module_import___closed__9);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header___elambda__1___closed__1 = _init_l_Lean_Parser_Module_header___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__1);
l_Lean_Parser_Module_header___elambda__1___closed__2 = _init_l_Lean_Parser_Module_header___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__2);
l_Lean_Parser_Module_header___elambda__1___closed__3 = _init_l_Lean_Parser_Module_header___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__3);
l_Lean_Parser_Module_header___elambda__1___closed__4 = _init_l_Lean_Parser_Module_header___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__4);
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
l_Lean_Parser_Module_header___closed__7 = _init_l_Lean_Parser_Module_header___closed__7();
lean_mark_persistent(l_Lean_Parser_Module_header___closed__7);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
l_Lean_Parser_Module_updateTokens___closed__1 = _init_l_Lean_Parser_Module_updateTokens___closed__1();
lean_mark_persistent(l_Lean_Parser_Module_updateTokens___closed__1);
l_Lean_Parser_ModuleParserState_inhabited___closed__1 = _init_l_Lean_Parser_ModuleParserState_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_ModuleParserState_inhabited___closed__1);
l_Lean_Parser_ModuleParserState_inhabited = _init_l_Lean_Parser_ModuleParserState_inhabited();
lean_mark_persistent(l_Lean_Parser_ModuleParserState_inhabited);
l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1 = _init_l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1();
lean_mark_persistent(l___private_Init_Lean_Parser_Module_2__mkEOI___closed__1);
l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2 = _init_l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2();
lean_mark_persistent(l___private_Init_Lean_Parser_Module_2__mkEOI___closed__2);
l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1 = _init_l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1);
l_Lean_Parser_testModuleParser___closed__1 = _init_l_Lean_Parser_testModuleParser___closed__1();
lean_mark_persistent(l_Lean_Parser_testModuleParser___closed__1);
l_Lean_Parser_testModuleParser___closed__2 = _init_l_Lean_Parser_testModuleParser___closed__2();
lean_mark_persistent(l_Lean_Parser_testModuleParser___closed__2);
l_Lean_Parser_parseFileAux___main___closed__1 = _init_l_Lean_Parser_parseFileAux___main___closed__1();
lean_mark_persistent(l_Lean_Parser_parseFileAux___main___closed__1);
l_Lean_Parser_parseFileAux___main___closed__2 = _init_l_Lean_Parser_parseFileAux___main___closed__2();
lean_mark_persistent(l_Lean_Parser_parseFileAux___main___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
