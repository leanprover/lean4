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
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_updateTokens___closed__1;
lean_object* l_Lean_Parser_Module_import___closed__9;
lean_object* l_Lean_Parser_isExitCommand___boxed(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1___closed__3;
lean_object* l_Lean_Parser_parseFile(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_testModuleParser___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__7;
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Parser_Module_import___closed__1;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
uint8_t l_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseFileAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_Inhabited(lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
extern lean_object* l_Lean_Parser_Level_ident___elambda__1___closed__4;
lean_object* l_PersistentArray_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__5(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_Parser_Module_header;
lean_object* l_Lean_Parser_Module_import___closed__6;
lean_object* l_Lean_Parser_Module_header___closed__5;
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_prelude___closed__5;
lean_object* l_Lean_Parser_Module_import___closed__2;
lean_object* l_Lean_Parser_ModuleParserState_inhabited;
lean_object* l_Lean_Parser_Module_prelude___elambda__1___closed__5;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
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
lean_object* l_Lean_Parser_Module_prelude___closed__2;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__7;
lean_object* l_Lean_Parser_Module_header___closed__3;
lean_object* l_String_trim(lean_object*);
lean_object* l___private_Init_Lean_Parser_Module_3__consumeInput(lean_object*, lean_object*);
lean_object* lean_io_prim_read_text_file(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___closed__5;
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_object* l_Lean_Parser_mkAntiquot(uint8_t, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isEOI___boxed(lean_object*);
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object*, lean_object*, lean_object*);
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___closed__3;
x_3 = l_Lean_Parser_Module_prelude___elambda__1___closed__5;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Module_prelude___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Module_prelude___elambda__1___closed__6;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_8);
x_15 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = l_Lean_Parser_tokenFn(x_2, x_15);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = l_String_posOfAux___main___closed__1;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 2)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
x_26 = l_coeDecidableEq(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_8);
x_28 = l_Lean_Parser_ParserState_mkErrorsAt(x_18, x_27, x_8);
x_29 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_17);
x_31 = l_Lean_Parser_mergeOrElseErrors(x_30, x_11, x_8);
lean_dec(x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_33 = l_Lean_Parser_ParserState_mkNode(x_18, x_32, x_17);
x_34 = l_Lean_Parser_mergeOrElseErrors(x_33, x_11, x_8);
lean_dec(x_8);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_22);
x_35 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_8);
x_36 = l_Lean_Parser_ParserState_mkErrorsAt(x_18, x_35, x_8);
x_37 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_17);
x_39 = l_Lean_Parser_mergeOrElseErrors(x_38, x_11, x_8);
lean_dec(x_8);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_8);
x_41 = l_Lean_Parser_ParserState_mkErrorsAt(x_18, x_40, x_8);
x_42 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_43 = l_Lean_Parser_ParserState_mkNode(x_41, x_42, x_17);
x_44 = l_Lean_Parser_mergeOrElseErrors(x_43, x_11, x_8);
lean_dec(x_8);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_19);
x_45 = l_String_posOfAux___main___closed__2;
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
x_47 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 2)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Parser_Module_prelude___elambda__1___closed__7;
x_50 = lean_string_dec_eq(x_48, x_49);
lean_dec(x_48);
x_51 = l_coeDecidableEq(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_8);
x_53 = l_Lean_Parser_ParserState_mkErrorsAt(x_18, x_52, x_8);
x_54 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_55 = l_Lean_Parser_ParserState_mkNode(x_53, x_54, x_17);
x_56 = l_Lean_Parser_mergeOrElseErrors(x_55, x_11, x_8);
lean_dec(x_8);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_58 = l_Lean_Parser_ParserState_mkNode(x_18, x_57, x_17);
x_59 = l_Lean_Parser_mergeOrElseErrors(x_58, x_11, x_8);
lean_dec(x_8);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_47);
x_60 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_8);
x_61 = l_Lean_Parser_ParserState_mkErrorsAt(x_18, x_60, x_8);
x_62 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_63 = l_Lean_Parser_ParserState_mkNode(x_61, x_62, x_17);
x_64 = l_Lean_Parser_mergeOrElseErrors(x_63, x_11, x_8);
lean_dec(x_8);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = l_Lean_Parser_Module_prelude___elambda__1___closed__10;
lean_inc(x_8);
x_66 = l_Lean_Parser_ParserState_mkErrorsAt(x_18, x_65, x_8);
x_67 = l_Lean_Parser_Module_prelude___elambda__1___closed__4;
x_68 = l_Lean_Parser_ParserState_mkNode(x_66, x_67, x_17);
x_69 = l_Lean_Parser_mergeOrElseErrors(x_68, x_11, x_8);
lean_dec(x_8);
return x_69;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude___elambda__1), 3, 0);
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_3 = l_Lean_Parser_Module_import___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_Parser_Module_import___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_apply_3(x_7, x_1, x_2, x_3);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_14, x_10);
lean_dec(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_39; lean_object* x_139; lean_object* x_140; 
lean_inc(x_10);
x_17 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean_dec(x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
lean_inc(x_2);
x_139 = l_Lean_Parser_tokenFn(x_2, x_17);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = l_String_posOfAux___main___closed__1;
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_142);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 2)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_146 = lean_string_dec_eq(x_144, x_145);
lean_dec(x_144);
x_147 = l_coeDecidableEq(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_10);
x_149 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_148, x_10);
x_39 = x_149;
goto block_138;
}
else
{
x_39 = x_139;
goto block_138;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_143);
x_150 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_10);
x_151 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_150, x_10);
x_39 = x_151;
goto block_138;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_10);
x_153 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_152, x_10);
x_39 = x_153;
goto block_138;
}
}
else
{
uint8_t x_154; 
lean_dec(x_140);
x_154 = l_String_posOfAux___main___closed__2;
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_139, 0);
lean_inc(x_155);
x_156 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_155);
lean_dec(x_155);
if (lean_obj_tag(x_156) == 2)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_159 = lean_string_dec_eq(x_157, x_158);
lean_dec(x_157);
x_160 = l_coeDecidableEq(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_10);
x_162 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_161, x_10);
x_39 = x_162;
goto block_138;
}
else
{
x_39 = x_139;
goto block_138;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_156);
x_163 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_10);
x_164 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_163, x_10);
x_39 = x_164;
goto block_138;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Lean_Parser_Module_import___elambda__1___closed__14;
lean_inc(x_10);
x_166 = l_Lean_Parser_ParserState_mkErrorsAt(x_139, x_165, x_10);
x_39 = x_166;
goto block_138;
}
}
block_38:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_String_posOfAux___main___closed__1;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_apply_3(x_5, x_1, x_2, x_20);
x_24 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_19);
x_26 = l_Lean_Parser_mergeOrElseErrors(x_25, x_13, x_10);
lean_dec(x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_20, x_27, x_19);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_13, x_10);
lean_dec(x_10);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
x_30 = l_String_posOfAux___main___closed__2;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_apply_3(x_5, x_1, x_2, x_20);
x_32 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_19);
x_34 = l_Lean_Parser_mergeOrElseErrors(x_33, x_13, x_10);
lean_dec(x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_36 = l_Lean_Parser_ParserState_mkNode(x_20, x_35, x_19);
x_37 = l_Lean_Parser_mergeOrElseErrors(x_36, x_13, x_10);
lean_dec(x_10);
return x_37;
}
}
}
block_138:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = l_String_posOfAux___main___closed__1;
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_2);
x_61 = l_Lean_Parser_tokenFn(x_2, x_39);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 2)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_67 = lean_string_dec_eq(x_65, x_66);
lean_dec(x_65);
x_68 = l_coeDecidableEq(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_44);
x_70 = l_Lean_Parser_ParserState_mkErrorsAt(x_61, x_69, x_44);
x_45 = x_70;
goto block_60;
}
else
{
x_45 = x_61;
goto block_60;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
x_71 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_44);
x_72 = l_Lean_Parser_ParserState_mkErrorsAt(x_61, x_71, x_44);
x_45 = x_72;
goto block_60;
}
}
else
{
uint8_t x_73; 
lean_dec(x_62);
x_73 = l_String_posOfAux___main___closed__2;
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
x_75 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 2)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_78 = lean_string_dec_eq(x_76, x_77);
lean_dec(x_76);
x_79 = l_coeDecidableEq(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_44);
x_81 = l_Lean_Parser_ParserState_mkErrorsAt(x_61, x_80, x_44);
x_45 = x_81;
goto block_60;
}
else
{
x_45 = x_61;
goto block_60;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_75);
x_82 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_44);
x_83 = l_Lean_Parser_ParserState_mkErrorsAt(x_61, x_82, x_44);
x_45 = x_83;
goto block_60;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_44);
x_85 = l_Lean_Parser_ParserState_mkErrorsAt(x_61, x_84, x_44);
x_45 = x_85;
goto block_60;
}
}
block_60:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
if (x_41 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
x_47 = l_Lean_nullKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_45, x_47, x_43);
x_20 = x_48;
goto block_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_Parser_ParserState_restore(x_45, x_43, x_44);
x_50 = l_Lean_nullKind;
x_51 = l_Lean_Parser_ParserState_mkNode(x_49, x_50, x_43);
x_20 = x_51;
goto block_38;
}
}
else
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; 
lean_dec(x_46);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
x_53 = lean_nat_dec_eq(x_52, x_44);
lean_dec(x_52);
x_54 = l_coeDecidableEq(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
x_55 = l_Lean_nullKind;
x_56 = l_Lean_Parser_ParserState_mkNode(x_45, x_55, x_43);
x_20 = x_56;
goto block_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Lean_Parser_ParserState_restore(x_45, x_43, x_44);
x_58 = l_Lean_nullKind;
x_59 = l_Lean_Parser_ParserState_mkNode(x_57, x_58, x_43);
x_20 = x_59;
goto block_38;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_86 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_87 = l_Lean_Parser_ParserState_mkNode(x_39, x_86, x_19);
x_88 = l_Lean_Parser_mergeOrElseErrors(x_87, x_13, x_10);
lean_dec(x_10);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_40);
x_89 = l_String_posOfAux___main___closed__2;
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_110; lean_object* x_111; 
x_90 = lean_ctor_get(x_39, 0);
lean_inc(x_90);
x_91 = lean_array_get_size(x_90);
lean_dec(x_90);
x_92 = lean_ctor_get(x_39, 1);
lean_inc(x_92);
lean_inc(x_2);
x_110 = l_Lean_Parser_tokenFn(x_2, x_39);
x_111 = lean_ctor_get(x_110, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = l_String_posOfAux___main___closed__1;
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 2)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_117 = lean_string_dec_eq(x_115, x_116);
lean_dec(x_115);
x_118 = l_coeDecidableEq(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_92);
x_120 = l_Lean_Parser_ParserState_mkErrorsAt(x_110, x_119, x_92);
x_93 = x_120;
goto block_109;
}
else
{
x_93 = x_110;
goto block_109;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_114);
x_121 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_92);
x_122 = l_Lean_Parser_ParserState_mkErrorsAt(x_110, x_121, x_92);
x_93 = x_122;
goto block_109;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_92);
x_124 = l_Lean_Parser_ParserState_mkErrorsAt(x_110, x_123, x_92);
x_93 = x_124;
goto block_109;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_111);
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
x_126 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_125);
lean_dec(x_125);
if (lean_obj_tag(x_126) == 2)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = l_Lean_Parser_Module_import___elambda__1___closed__8;
x_129 = lean_string_dec_eq(x_127, x_128);
lean_dec(x_127);
x_130 = l_coeDecidableEq(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_92);
x_132 = l_Lean_Parser_ParserState_mkErrorsAt(x_110, x_131, x_92);
x_93 = x_132;
goto block_109;
}
else
{
x_93 = x_110;
goto block_109;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_126);
x_133 = l_Lean_Parser_Module_import___elambda__1___closed__11;
lean_inc(x_92);
x_134 = l_Lean_Parser_ParserState_mkErrorsAt(x_110, x_133, x_92);
x_93 = x_134;
goto block_109;
}
}
block_109:
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 3);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = l_String_posOfAux___main___closed__1;
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_92);
x_96 = l_Lean_nullKind;
x_97 = l_Lean_Parser_ParserState_mkNode(x_93, x_96, x_91);
x_20 = x_97;
goto block_38;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = l_Lean_Parser_ParserState_restore(x_93, x_91, x_92);
x_99 = l_Lean_nullKind;
x_100 = l_Lean_Parser_ParserState_mkNode(x_98, x_99, x_91);
x_20 = x_100;
goto block_38;
}
}
else
{
lean_object* x_101; uint8_t x_102; uint8_t x_103; 
lean_dec(x_94);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
x_102 = lean_nat_dec_eq(x_101, x_92);
lean_dec(x_101);
x_103 = l_coeDecidableEq(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_92);
x_104 = l_Lean_nullKind;
x_105 = l_Lean_Parser_ParserState_mkNode(x_93, x_104, x_91);
x_20 = x_105;
goto block_38;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l_Lean_Parser_ParserState_restore(x_93, x_91, x_92);
x_107 = l_Lean_nullKind;
x_108 = l_Lean_Parser_ParserState_mkNode(x_106, x_107, x_91);
x_20 = x_108;
goto block_38;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_135 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_136 = l_Lean_Parser_ParserState_mkNode(x_39, x_135, x_19);
x_137 = l_Lean_Parser_mergeOrElseErrors(x_136, x_13, x_10);
lean_dec(x_10);
return x_137;
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
x_1 = l_Lean_Parser_Level_ident___elambda__1___closed__4;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import___elambda__1), 3, 0);
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
lean_inc(x_2);
x_8 = l_Lean_Parser_Module_import___elambda__1(x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = l_String_posOfAux___main___closed__1;
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Parser_manyAux___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_7, x_17);
lean_dec(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_9);
x_21 = l_String_posOfAux___main___closed__2;
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; 
lean_dec(x_6);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
x_23 = lean_nat_dec_eq(x_7, x_22);
lean_dec(x_22);
lean_dec(x_7);
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = l_Lean_Parser_manyAux___main___closed__1;
x_27 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_26);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; 
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
x_29 = lean_nat_dec_eq(x_7, x_28);
lean_dec(x_28);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_31;
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_3 = l_Lean_Parser_Module_header___elambda__1___closed__3;
x_4 = 1;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Module_header___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_Module_header___elambda__1___closed__4;
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_5, x_1, x_2, x_3);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_47; lean_object* x_48; 
lean_inc(x_8);
x_15 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Lean_Parser_Module_prelude___elambda__1(x_1, x_2, x_15);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = l_String_posOfAux___main___closed__1;
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_nullKind;
lean_inc(x_17);
x_51 = l_Lean_Parser_ParserState_mkNode(x_47, x_50, x_17);
x_18 = x_51;
goto block_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_8);
x_52 = l_Lean_Parser_ParserState_restore(x_47, x_17, x_8);
x_53 = l_Lean_nullKind;
lean_inc(x_17);
x_54 = l_Lean_Parser_ParserState_mkNode(x_52, x_53, x_17);
x_18 = x_54;
goto block_46;
}
}
else
{
lean_object* x_55; uint8_t x_56; uint8_t x_57; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
x_56 = lean_nat_dec_eq(x_55, x_8);
lean_dec(x_55);
x_57 = l_coeDecidableEq(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_nullKind;
lean_inc(x_17);
x_59 = l_Lean_Parser_ParserState_mkNode(x_47, x_58, x_17);
x_18 = x_59;
goto block_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc(x_8);
x_60 = l_Lean_Parser_ParserState_restore(x_47, x_17, x_8);
x_61 = l_Lean_nullKind;
lean_inc(x_17);
x_62 = l_Lean_Parser_ParserState_mkNode(x_60, x_61, x_17);
x_18 = x_62;
goto block_46;
}
}
block_46:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = l_String_posOfAux___main___closed__1;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_23, x_1, x_2, x_18);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_22);
x_27 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_17);
x_29 = l_Lean_Parser_mergeOrElseErrors(x_28, x_11, x_8);
lean_dec(x_8);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_31 = l_Lean_Parser_ParserState_mkNode(x_18, x_30, x_17);
x_32 = l_Lean_Parser_mergeOrElseErrors(x_31, x_11, x_8);
lean_dec(x_8);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = l_String_posOfAux___main___closed__2;
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
x_35 = lean_array_get_size(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_36, x_1, x_2, x_18);
x_38 = l_Lean_nullKind;
x_39 = l_Lean_Parser_ParserState_mkNode(x_37, x_38, x_35);
x_40 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_17);
x_42 = l_Lean_Parser_mergeOrElseErrors(x_41, x_11, x_8);
lean_dec(x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_44 = l_Lean_Parser_ParserState_mkNode(x_18, x_43, x_17);
x_45 = l_Lean_Parser_mergeOrElseErrors(x_44, x_11, x_8);
lean_dec(x_8);
return x_45;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header___elambda__1), 3, 0);
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
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_5, x_2, x_3, x_4);
return x_6;
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
x_3 = lean_ctor_get(x_1, 2);
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
lean_ctor_set(x_1, 2, x_8);
return x_1;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_1, 2, x_9);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Lean_Parser_Module_header;
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = l_Lean_Parser_addParserTokens(x_12, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_16 = l_Lean_Parser_Module_updateTokens___closed__1;
x_17 = l_unreachable_x21___rarg(x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_19);
return x_20;
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
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_10 = l_Lean_Parser_Module_header___elambda__1(x_9, x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_11);
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
x_17 = l_PersistentArray_empty___closed__3;
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
x_26 = l_PersistentArray_empty___closed__3;
x_27 = l_PersistentArray_push___rarg(x_26, x_23);
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_7, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Parser_mkParserContext(x_1, x_2);
x_13 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = l_Array_empty___closed__1;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
x_17 = l_Lean_Parser_whitespace___main(x_12, x_16);
x_18 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_20 = l_Lean_Parser_categoryParserFn(x_18, x_19, x_12, x_17);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_22);
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
x_29 = l_coeDecidableEq(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Parser_Error_toString(x_28);
x_32 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_12, x_30, x_31);
x_33 = l_PersistentArray_push___rarg(x_4, x_32);
x_34 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_12, x_30);
x_35 = 1;
lean_ctor_set(x_3, 0, x_34);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_35);
x_4 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_28);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_dec(x_20);
x_38 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_12, x_37);
x_39 = 1;
lean_ctor_set(x_3, 0, x_38);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_39);
goto _start;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Lean_Parser_mkParserContext(x_1, x_2);
x_42 = l_Lean_Parser_initCacheForInput(x_7);
lean_dec(x_7);
x_43 = lean_box(0);
x_44 = l_Array_empty___closed__1;
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_5);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = l_Lean_Parser_whitespace___main(x_41, x_45);
x_47 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
x_48 = lean_unsigned_to_nat(0u);
lean_inc(x_41);
x_49 = l_Lean_Parser_categoryParserFn(x_47, x_48, x_41, x_46);
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = 0;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = l_coeDecidableEq(x_6);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
x_61 = l_Lean_Parser_Error_toString(x_58);
x_62 = l___private_Init_Lean_Parser_Module_1__mkErrorMessage(x_41, x_60, x_61);
x_63 = l_PersistentArray_push___rarg(x_4, x_62);
x_64 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_41, x_60);
x_65 = 1;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_3 = x_66;
x_4 = x_63;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
lean_dec(x_58);
x_68 = lean_ctor_get(x_49, 1);
lean_inc(x_68);
lean_dec(x_49);
x_69 = l___private_Init_Lean_Parser_Module_3__consumeInput(x_41, x_68);
x_70 = 1;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_3 = x_71;
goto _start;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_73 = l___private_Init_Lean_Parser_Module_2__mkEOI(x_5);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_3);
lean_ctor_set(x_74, 1, x_4);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
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
uint8_t x_13; uint8_t x_14; 
lean_inc(x_9);
x_13 = l_Lean_Parser_isExitCommand(x_9);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_coeDecidableEq(x_3);
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
x_24 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
x_25 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_24, x_11, x_6);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_11);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
x_45 = l_String_posOfAux___main___closed__2;
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_coeDecidableEq(x_3);
if (x_46 == 0)
{
lean_dec(x_9);
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_48; 
x_48 = l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(x_9, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_4 = x_10;
x_5 = x_11;
x_6 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
x_56 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_55, x_11, x_6);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; 
x_60 = 1;
x_61 = lean_box(x_60);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
uint8_t x_62; lean_object* x_63; 
x_62 = 0;
x_63 = lean_box(x_62);
lean_ctor_set(x_56, 0, x_63);
return x_56;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_11);
lean_dec(x_11);
if (x_65 == 0)
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_56);
if (x_72 == 0)
{
return x_56;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_56, 0);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_56);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
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
x_14 = l_coeDecidableEq(x_4);
x_15 = lean_box(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_testModuleParser___lambda__1___boxed), 7, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_12);
lean_closure_set(x_16, 4, x_13);
if (x_14 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_17 = l_Lean_Parser_testModuleParser___closed__2;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = lean_io_timeit(x_7, x_18, x_5);
lean_dec(x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_16);
x_22 = lean_io_timeit(x_7, x_21, x_5);
lean_dec(x_7);
return x_22;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
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
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_9);
x_3 = x_10;
x_4 = x_11;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_16; uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_PersistentArray_isEmpty___rarg(x_11);
x_17 = l_coeDecidableEq(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_18 = l___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___closed__1;
x_19 = l_PersistentArray_forM___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_18, x_11, x_6);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l_Lean_Parser_parseFileAux___main___closed__2;
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Parser_parseFileAux___main___closed__2;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
x_30 = l_Lean_nullKind;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = l_Lean_Syntax_updateLeading(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
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
