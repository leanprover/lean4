// Lean compiler output
// Module: init.lean.parser.module
// Imports: init.lean.message init.lean.parser.command
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_Parser_Module_prelude___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Module_import___closed__5;
obj* l_Lean_Parser_Module_importPath___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath___elambda__1___closed__2;
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_importPath___elambda__1(obj*, obj*, obj*);
extern "C" obj* lean_io_realpath(obj*, obj*);
obj* l_Lean_FileMap_toPosition___main(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_Parser_whitespace___main(obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath___elambda__1___closed__1;
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__mkErrorMessage(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
obj* l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(obj*);
namespace lean {
obj* test_module_parser_core(obj*, obj*, obj*, uint8, obj*);
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
extern obj* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
obj* l_Lean_Parser_ParserAttribute_runParser(obj*, obj*, obj*, obj*);
uint8 l_Lean_Parser_isExitCommand(obj*);
obj* l_Lean_Parser_Module_importPath___closed__1;
obj* l_Lean_Parser_Module_header;
obj* l_Lean_Parser_parseFileAux___main___closed__1;
obj* l___private_init_lean_parser_module_4__testModuleParserAux(obj*, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import___closed__2;
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
obj* l_Lean_Syntax_formatStx___main___rarg(obj*);
obj* l_Lean_Parser_rawCh___elambda__1___rarg(uint32, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkUnexpectedError(obj*, obj*);
obj* l_Lean_Parser_initCacheForInput(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Parser_Module_prelude___closed__1;
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7;
uint8 l_List_isEmpty___main___rarg(obj*);
obj* l_Lean_Parser_Module_header___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_rawCh(uint8, uint32, uint8);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l___private_init_lean_parser_module_2__mkEOI___closed__1;
obj* l_Lean_Parser_isExitCommand___boxed(obj*);
obj* l_Lean_Parser_Module_importPath___closed__2;
obj* l___private_init_lean_parser_module_4__testModuleParserAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath___closed__6;
extern obj* l_Lean_Options_empty;
obj* l_Lean_Parser_mkParserState(obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_Parser_Module_header___elambda__1___closed__2;
obj* l_Lean_Parser_testModuleParser___lambda__1(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header___closed__2;
obj* l_Lean_Parser_testModuleParser___closed__1;
obj* l___private_init_lean_parser_module_3__consumeInput(obj*, obj*);
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_import___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header___closed__1;
obj* l___private_init_lean_parser_module_4__testModuleParserAux___main(obj*, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import___closed__3;
obj* l_Lean_Parser_Module_header___elambda__1___closed__1;
obj* l_Lean_Parser_isEOI___boxed(obj*);
extern obj* l_Lean_Parser_manyAux___main___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_IO_print___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__2(obj*, obj*);
obj* l_Lean_Parser_Module_prelude___closed__3;
obj* l_Lean_Parser_Error_toString(obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_Lean_Parser_testModuleParser___closed__2;
obj* l_Lean_Parser_tokenFn(obj*, obj*);
obj* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1___boxed(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_Module_import___elambda__1___closed__4;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import;
obj* l___private_init_lean_parser_module_1__mkErrorMessage___boxed(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_testModuleParser___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath___closed__4;
obj* l_Lean_Parser_Module_importPath___closed__3;
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_Lean_nullKind;
obj* l_IO_print___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__4(obj*, obj*);
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
obj* l_Lean_Parser_Module_import___elambda__1___closed__6;
obj* l_Lean_Parser_Module_import___elambda__1___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import___elambda__1___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_ident___closed__1;
obj* l_Lean_Parser_Module_header___closed__6;
extern obj* l_Substring_drop___main___closed__2;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_module_2__mkEOI(obj*);
obj* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1(obj*, obj*);
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Module_prelude___closed__2;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l___private_init_lean_parser_module_4__testModuleParserAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_import___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_parseCommand___main(obj*, obj*, obj*, obj*);
uint8 l_Lean_Parser_isEOI(obj*);
obj* l_Lean_Parser_optionaInfo(obj*);
obj* l_Lean_Parser_testModuleParser___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Syntax_isOfKind___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_import___elambda__1___closed__2;
obj* l_EState_bind___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header___closed__3;
obj* l_Lean_Parser_Module_header___closed__5;
extern obj* l_Lean_Parser_Trie_HasEmptyc___closed__1;
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
extern "C" obj* lean_io_prim_read_text_file(obj*, obj*);
obj* l_Lean_Parser_Module_header___elambda__1(obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_Module_updateTokens(obj*);
obj* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__3(obj*, obj*);
obj* l_Lean_Parser_Module_importPath;
obj* l_Lean_Parser_Module_prelude___closed__4;
obj* l_Lean_Parser_Module_prelude___elambda__1(obj*);
obj* l_Lean_Parser_mkParserContextCore(obj*, obj*, obj*);
obj* l_Lean_Parser_parseFileAux___main(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfor___main___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__5(obj*, obj*);
obj* l_Lean_Syntax_updateLeading___rarg(obj*);
obj* l_Lean_Parser_parseFile(obj*, obj*, obj*);
obj* l_Lean_Parser_ModuleParserState_inhabited___closed__1;
obj* l_Lean_Parser_parseFileAux(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*, obj*);
obj* l_Lean_Message_toString(obj*);
obj* l_Lean_Parser_ModuleParserState_inhabited;
obj* l_Array_size(obj*, obj*);
obj* l_EState_pure___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_import___elambda__1___closed__5;
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseCommand(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import___closed__1;
obj* l_Lean_Parser_Module_prelude;
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Module_import___elambda__1___closed__1;
obj* l_Lean_Parser_Module_import___elambda__1___closed__7;
uint8 l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(uint8, obj*);
extern "C" obj* lean_io_timeit(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import___closed__4;
extern obj* l_Lean_Parser_Command_exit___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Module_header___closed__4;
obj* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(obj*, obj*);
extern obj* l_Lean_Parser_commandParserAttribute;
extern obj* l_IO_println___rarg___closed__1;
obj* l___private_init_lean_parser_module_2__mkEOI___closed__3;
obj* l___private_init_lean_parser_module_2__mkEOI___closed__2;
obj* l_Lean_Parser_Module_import___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkErrorsAt(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_Module_importPath___closed__5;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_parseHeader(obj*, obj*);
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Module");
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("prelude");
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Module_prelude___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 2)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_12 = lean::string_dec_eq(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_13, x_5);
x_15 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_5);
x_17 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_4);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_9);
x_19 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_19, x_5);
x_21 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_7);
x_23 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8;
x_24 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_23, x_5);
x_25 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
}
}
}
obj* l_Lean_Parser_Module_prelude___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_prelude___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4;
x_2 = l_Lean_Parser_Module_prelude___closed__1;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_prelude___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___closed__2;
x_2 = l_Lean_Parser_Module_prelude___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_prelude___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Module_prelude___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Module_prelude___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; 
x_5 = 46;
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
x_9 = 1;
x_10 = l_Lean_Parser_rawCh___elambda__1___rarg(x_5, x_9, x_2, x_3, x_4);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; uint8 x_13; 
lean::dec(x_7);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_13 = lean::nat_dec_eq(x_8, x_12);
lean::dec(x_12);
lean::dec(x_8);
if (x_13 == 0)
{
x_4 = x_10;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_Lean_Parser_manyAux___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_10, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_11);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_18 = lean::nat_dec_eq(x_8, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
lean::dec(x_8);
lean::dec(x_7);
return x_10;
}
else
{
obj* x_19; 
x_19 = l_Lean_Parser_ParserState_restore(x_10, x_7, x_8);
lean::dec(x_7);
return x_19;
}
}
}
}
obj* _init_l_Lean_Parser_Module_importPath___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("importPath");
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_importPath___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_importPath___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Module_importPath___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = 0;
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(x_6, x_1, x_2, x_3);
x_8 = l_Lean_nullKind;
lean::inc(x_5);
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_5);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = l_Lean_Parser_identFn___rarg(x_2, x_9);
x_12 = l_Lean_Parser_Module_importPath___elambda__1___closed__2;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_5);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_10);
lean::dec(x_2);
x_14 = l_Lean_Parser_Module_importPath___elambda__1___closed__2;
x_15 = l_Lean_Parser_ParserState_mkNode(x_9, x_14, x_5);
return x_15;
}
}
}
obj* _init_l_Lean_Parser_Module_importPath___closed__1() {
_start:
{
uint32 x_1; uint8 x_2; uint8 x_3; obj* x_4; 
x_1 = 46;
x_2 = 0;
x_3 = 1;
x_4 = l_Lean_Parser_rawCh(x_2, x_1, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_Module_importPath___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_importPath___closed__1;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_importPath___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_importPath___closed__2;
x_2 = l_Lean_Parser_ident___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_importPath___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_importPath___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_importPath___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_importPath___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_importPath___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_importPath___closed__4;
x_2 = l_Lean_Parser_Module_importPath___closed__5;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_importPath() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_importPath___closed__6;
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_importPath___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Module_importPath___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Module_importPath___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_import___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::inc(x_3);
x_8 = l_Lean_Parser_Module_importPath___elambda__1(x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; 
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_11 = lean::nat_dec_eq(x_7, x_10);
lean::dec(x_10);
lean::dec(x_7);
if (x_11 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = l_Lean_Parser_manyAux___main___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_13);
return x_14;
}
}
else
{
obj* x_15; uint8 x_16; 
lean::dec(x_9);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
x_16 = lean::nat_dec_eq(x_7, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_7);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_17; 
x_17 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean::dec(x_6);
return x_17;
}
}
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("import");
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("import ");
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import___elambda__1___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__6;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Module_import___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_25; obj* x_26; obj* x_27; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_25 = lean::cnstr_get(x_3, 1);
lean::inc(x_25);
lean::inc(x_2);
x_26 = l_Lean_Parser_tokenFn(x_2, x_3);
x_27 = lean::cnstr_get(x_26, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
x_29 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_28);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 2)
{
obj* x_30; obj* x_31; uint8 x_32; 
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_32 = lean::string_dec_eq(x_30, x_31);
lean::dec(x_30);
if (x_32 == 0)
{
obj* x_33; obj* x_34; 
x_33 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_34 = l_Lean_Parser_ParserState_mkErrorsAt(x_26, x_33, x_25);
x_6 = x_34;
goto block_24;
}
else
{
lean::dec(x_25);
x_6 = x_26;
goto block_24;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_29);
x_35 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_36 = l_Lean_Parser_ParserState_mkErrorsAt(x_26, x_35, x_25);
x_6 = x_36;
goto block_24;
}
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_27);
x_37 = l_Lean_Parser_Module_import___elambda__1___closed__7;
x_38 = l_Lean_Parser_ParserState_mkErrorsAt(x_26, x_37, x_25);
x_6 = x_38;
goto block_24;
}
block_24:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
lean::inc(x_2);
x_10 = l_Lean_Parser_Module_importPath___elambda__1(x_1, x_2, x_6);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = 0;
x_13 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_import___elambda__1___spec__1(x_12, x_1, x_2, x_10);
x_14 = l_Lean_nullKind;
x_15 = l_Lean_Parser_ParserState_mkNode(x_13, x_14, x_9);
x_16 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_5);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_11);
lean::dec(x_2);
x_18 = l_Lean_nullKind;
x_19 = l_Lean_Parser_ParserState_mkNode(x_10, x_18, x_9);
x_20 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_5);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_7);
lean::dec(x_2);
x_22 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_6, x_22, x_5);
return x_23;
}
}
}
}
obj* _init_l_Lean_Parser_Module_import___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Module_import___elambda__1___closed__4;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_Module_importPath;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Module_import___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_Module_import___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_import___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_import___closed__2;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_import___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_import___closed__3;
x_2 = l_Lean_Parser_Module_import___closed__4;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_import___closed__5;
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_import___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_import___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Module_import___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Module_import___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::inc(x_3);
x_8 = l_Lean_Parser_Module_import___elambda__1(x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; 
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_11 = lean::nat_dec_eq(x_7, x_10);
lean::dec(x_10);
lean::dec(x_7);
if (x_11 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = l_Lean_Parser_manyAux___main___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_13);
return x_14;
}
}
else
{
obj* x_15; uint8 x_16; 
lean::dec(x_9);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
x_16 = lean::nat_dec_eq(x_7, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_7);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_17; 
x_17 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean::dec(x_6);
return x_17;
}
}
}
}
obj* _init_l_Lean_Parser_Module_header___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("header");
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_header___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Module_header___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Module_header___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::inc(x_2);
x_7 = l_Lean_Parser_Module_prelude___elambda__1___rarg(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_6);
x_9 = l_Lean_nullKind;
lean::inc(x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_7, x_9, x_5);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::array_get_size(x_12);
lean::dec(x_12);
x_14 = 0;
x_15 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_14, x_1, x_2, x_10);
x_16 = l_Lean_Parser_ParserState_mkNode(x_15, x_9, x_13);
x_17 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_5);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_11);
lean::dec(x_2);
x_19 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_10, x_19, x_5);
return x_20;
}
}
else
{
obj* x_21; uint8 x_22; 
lean::dec(x_8);
x_21 = lean::cnstr_get(x_7, 1);
lean::inc(x_21);
x_22 = lean::nat_dec_eq(x_21, x_6);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_23 = l_Lean_nullKind;
lean::inc(x_5);
x_24 = l_Lean_Parser_ParserState_mkNode(x_7, x_23, x_5);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
x_27 = lean::array_get_size(x_26);
lean::dec(x_26);
x_28 = 0;
x_29 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_28, x_1, x_2, x_24);
x_30 = l_Lean_Parser_ParserState_mkNode(x_29, x_23, x_27);
x_31 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_5);
return x_32;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_25);
lean::dec(x_2);
x_33 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_34 = l_Lean_Parser_ParserState_mkNode(x_24, x_33, x_5);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
x_36 = l_Lean_nullKind;
lean::inc(x_5);
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_5);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_40 = lean::array_get_size(x_39);
lean::dec(x_39);
x_41 = 0;
x_42 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_41, x_1, x_2, x_37);
x_43 = l_Lean_Parser_ParserState_mkNode(x_42, x_36, x_40);
x_44 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_5);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_38);
lean::dec(x_2);
x_46 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_47 = l_Lean_Parser_ParserState_mkNode(x_37, x_46, x_5);
return x_47;
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_header___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_optionaInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_header___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_import;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_header___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__1;
x_2 = l_Lean_Parser_Module_header___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_header___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_header___elambda__1___closed__2;
x_2 = l_Lean_Parser_Module_header___closed__3;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_header___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_header___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_header___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_header___closed__4;
x_2 = l_Lean_Parser_Module_header___closed__5;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_header() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_header___closed__6;
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Module_header___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Module_header___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Module_header___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Module_updateTokens(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 3);
x_6 = l_Lean_Parser_Module_header;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_1(x_8, x_5);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
lean::dec(x_9);
x_10 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean::cnstr_set(x_3, 3, x_10);
return x_1;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
lean::cnstr_set(x_3, 3, x_11);
return x_1;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
x_14 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 3);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_3);
x_16 = l_Lean_Parser_Module_header;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
lean::dec(x_17);
x_19 = lean::apply_1(x_18, x_15);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_19);
x_20 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_14);
lean::cnstr_set(x_21, 3, x_20);
lean::cnstr_set(x_1, 0, x_21);
return x_1;
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::dec(x_19);
x_23 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_14);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set(x_1, 0, x_23);
return x_1;
}
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_24 = lean::cnstr_get(x_1, 0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_1);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_24, 2);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_24, 3);
lean::inc(x_29);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 lean::cnstr_release(x_24, 2);
 lean::cnstr_release(x_24, 3);
 x_30 = x_24;
} else {
 lean::dec_ref(x_24);
 x_30 = lean::box(0);
}
x_31 = l_Lean_Parser_Module_header;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
lean::dec(x_32);
x_34 = lean::apply_1(x_33, x_29);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_34);
x_35 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
if (lean::is_scalar(x_30)) {
 x_36 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_36 = x_30;
}
lean::cnstr_set(x_36, 0, x_26);
lean::cnstr_set(x_36, 1, x_27);
lean::cnstr_set(x_36, 2, x_28);
lean::cnstr_set(x_36, 3, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_25);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
if (lean::is_scalar(x_30)) {
 x_39 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_39 = x_30;
}
lean::cnstr_set(x_39, 0, x_26);
lean::cnstr_set(x_39, 1, x_27);
lean::cnstr_set(x_39, 2, x_28);
lean::cnstr_set(x_39, 3, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_25);
return x_40;
}
}
}
}
obj* _init_l_Lean_Parser_ModuleParserState_inhabited___closed__1() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = 0;
x_3 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_ModuleParserState_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ModuleParserState_inhabited___closed__1;
return x_1;
}
}
obj* l___private_init_lean_parser_module_1__mkErrorMessage(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_4, 2);
x_6 = l_Lean_FileMap_toPosition___main(x_5, x_2);
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean::box(0);
x_9 = 2;
x_10 = l_String_splitAux___main___closed__1;
lean::inc(x_7);
x_11 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_10);
lean::cnstr_set(x_11, 4, x_3);
lean::cnstr_set_scalar(x_11, sizeof(void*)*5, x_9);
return x_11;
}
}
obj* l___private_init_lean_parser_module_1__mkErrorMessage___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_module_1__mkErrorMessage(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_parseHeader(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_Module_updateTokens(x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = l_Lean_Parser_mkParserState(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_whitespace___main(x_4, x_7);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_10 = l_Lean_Parser_Module_header___elambda__1(x_9, x_4, x_8);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_11);
lean::dec(x_11);
x_13 = lean::cnstr_get(x_10, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_4);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_15 = 0;
x_16 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_22 = l_Lean_Parser_Error_toString(x_20);
x_23 = l___private_init_lean_parser_module_1__mkErrorMessage(x_4, x_21, x_22);
lean::dec(x_4);
x_24 = 1;
x_25 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_24);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_12);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
obj* _init_l___private_init_lean_parser_module_2__mkEOI___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("eoi");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_module_2__mkEOI___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2;
x_2 = l___private_init_lean_parser_module_2__mkEOI___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_parser_module_2__mkEOI___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::mk_empty_array(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_module_2__mkEOI(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = l_Substring_drop___main___closed__2;
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_String_splitAux___main___closed__1;
x_6 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l___private_init_lean_parser_module_2__mkEOI___closed__3;
x_8 = lean::array_push(x_7, x_6);
x_9 = l___private_init_lean_parser_module_2__mkEOI___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
uint8 l_Lean_Parser_isEOI(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l___private_init_lean_parser_module_2__mkEOI___closed__2;
x_3 = l_Lean_Syntax_isOfKind___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_isEOI___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Parser_isEOI(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Parser_isExitCommand(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_Lean_Parser_Command_exit___elambda__1___rarg___closed__2;
x_3 = l_Lean_Syntax_isOfKind___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_isExitCommand___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Parser_isExitCommand(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_module_3__consumeInput(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_initCacheForInput(x_4);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = l_Array_empty___closed__1;
lean::inc(x_2);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_6);
x_9 = l_Lean_Parser_tokenFn(x_1, x_8);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; 
lean::dec(x_2);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
return x_11;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_10);
lean::dec(x_9);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
return x_13;
}
}
}
obj* l_Lean_Parser_parseCommand___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = lean::string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_3);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_3, 0);
lean::dec(x_10);
lean::inc(x_1);
lean::inc(x_2);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_1);
x_12 = l_Lean_Parser_initCacheForInput(x_7);
lean::dec(x_7);
x_13 = lean::box(0);
x_14 = l_Array_empty___closed__1;
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_5);
lean::cnstr_set(x_15, 2, x_12);
lean::cnstr_set(x_15, 3, x_13);
x_16 = l_Lean_Parser_commandParserAttribute;
x_17 = lean::mk_nat_obj(0u);
lean::inc(x_11);
x_18 = l_Lean_Parser_ParserAttribute_runParser(x_16, x_17, x_11, x_15);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_18, 0);
lean::inc(x_20);
x_21 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_20);
lean::dec(x_20);
x_22 = lean::cnstr_get(x_18, 1);
lean::inc(x_22);
lean::dec(x_18);
x_23 = 0;
lean::cnstr_set(x_3, 0, x_22);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_23);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_3);
lean::cnstr_set(x_24, 1, x_4);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
else
{
if (x_6 == 0)
{
obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_18, 1);
lean::inc(x_27);
lean::dec(x_18);
lean::inc(x_27);
lean::inc(x_11);
x_28 = l___private_init_lean_parser_module_3__consumeInput(x_11, x_27);
x_29 = 1;
lean::cnstr_set(x_3, 0, x_28);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_29);
x_30 = l_Lean_Parser_Error_toString(x_26);
x_31 = l___private_init_lean_parser_module_1__mkErrorMessage(x_11, x_27, x_30);
lean::dec(x_27);
lean::dec(x_11);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_4);
x_4 = x_32;
goto _start;
}
else
{
obj* x_34; obj* x_35; uint8 x_36; 
lean::dec(x_19);
x_34 = lean::cnstr_get(x_18, 1);
lean::inc(x_34);
lean::dec(x_18);
x_35 = l___private_init_lean_parser_module_3__consumeInput(x_11, x_34);
x_36 = 1;
lean::cnstr_set(x_3, 0, x_35);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_36);
goto _start;
}
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_2);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_2);
lean::cnstr_set(x_38, 1, x_1);
x_39 = l_Lean_Parser_initCacheForInput(x_7);
lean::dec(x_7);
x_40 = lean::box(0);
x_41 = l_Array_empty___closed__1;
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_5);
lean::cnstr_set(x_42, 2, x_39);
lean::cnstr_set(x_42, 3, x_40);
x_43 = l_Lean_Parser_commandParserAttribute;
x_44 = lean::mk_nat_obj(0u);
lean::inc(x_38);
x_45 = l_Lean_Parser_ParserAttribute_runParser(x_43, x_44, x_38, x_42);
x_46 = lean::cnstr_get(x_45, 3);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_38);
lean::dec(x_2);
lean::dec(x_1);
x_47 = lean::cnstr_get(x_45, 0);
lean::inc(x_47);
x_48 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_47);
lean::dec(x_47);
x_49 = lean::cnstr_get(x_45, 1);
lean::inc(x_49);
lean::dec(x_45);
x_50 = 0;
x_51 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_50);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_4);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_48);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
else
{
if (x_6 == 0)
{
obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = lean::cnstr_get(x_46, 0);
lean::inc(x_54);
lean::dec(x_46);
x_55 = lean::cnstr_get(x_45, 1);
lean::inc(x_55);
lean::dec(x_45);
lean::inc(x_55);
lean::inc(x_38);
x_56 = l___private_init_lean_parser_module_3__consumeInput(x_38, x_55);
x_57 = 1;
x_58 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_57);
x_59 = l_Lean_Parser_Error_toString(x_54);
x_60 = l___private_init_lean_parser_module_1__mkErrorMessage(x_38, x_55, x_59);
lean::dec(x_55);
lean::dec(x_38);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_4);
x_3 = x_58;
x_4 = x_61;
goto _start;
}
else
{
obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
lean::dec(x_46);
x_63 = lean::cnstr_get(x_45, 1);
lean::inc(x_63);
lean::dec(x_45);
x_64 = l___private_init_lean_parser_module_3__consumeInput(x_38, x_63);
x_65 = 1;
x_66 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_65);
x_3 = x_66;
goto _start;
}
}
}
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_68 = l___private_init_lean_parser_module_2__mkEOI(x_5);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_3);
lean::cnstr_set(x_69, 1, x_4);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
}
}
obj* l_Lean_Parser_parseCommand(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_parseCommand___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_IO_print___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
x_6 = lean_io_prim_put_str(x_5, x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_print___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__2(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_io_prim_put_str(x_7, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_io_prim_put_str(x_12, x_11);
return x_13;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_IO_print___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Message_toString(x_1);
x_4 = lean_io_prim_put_str(x_3, x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_print___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__4(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_io_prim_put_str(x_7, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_io_prim_put_str(x_12, x_11);
return x_13;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_mfor___main___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__5(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::dec(x_4);
x_5 = lean::box(0);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_11 = l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__3(x_9, x_2);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_11, 0, x_14);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
lean::dec(x_11);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_1 = x_10;
x_2 = x_18;
goto _start;
}
}
else
{
uint8 x_20; 
lean::dec(x_10);
x_20 = !lean::is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_11, 0);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
obj* l___private_init_lean_parser_module_4__testModuleParserAux___main(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_Lean_Parser_parseCommand___main(x_1, x_2, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_12 = l_Lean_Parser_isEOI(x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Parser_isExitCommand(x_9);
if (x_13 == 0)
{
if (x_3 == 0)
{
uint8 x_14; 
lean::dec(x_9);
x_14 = !lean::is_exclusive(x_6);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_6, 0);
lean::dec(x_15);
x_16 = lean::box(0);
lean::cnstr_set(x_6, 0, x_16);
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_6, 1);
lean::inc(x_18);
lean::dec(x_6);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_4 = x_10;
x_5 = x_11;
x_6 = x_20;
goto _start;
}
}
else
{
obj* x_22; 
x_22 = l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1(x_9, x_6);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::dec(x_24);
x_25 = lean::box(0);
lean::cnstr_set(x_22, 0, x_25);
x_4 = x_10;
x_5 = x_11;
x_6 = x_22;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_4 = x_10;
x_5 = x_11;
x_6 = x_29;
goto _start;
}
}
else
{
uint8 x_31; 
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_22, 0);
x_33 = lean::cnstr_get(x_22, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_22);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_11);
x_35 = l_List_reverse___rarg(x_11);
x_36 = l_List_mfor___main___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__5(x_35, x_6);
if (lean::obj_tag(x_36) == 0)
{
uint8 x_37; 
x_37 = !lean::is_exclusive(x_36);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; uint8 x_40; 
x_38 = lean::cnstr_get(x_36, 0);
lean::dec(x_38);
x_39 = 0;
x_40 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_39, x_11);
lean::dec(x_11);
if (x_40 == 0)
{
uint8 x_41; obj* x_42; 
x_41 = 1;
x_42 = lean::box(x_41);
lean::cnstr_set(x_36, 0, x_42);
return x_36;
}
else
{
obj* x_43; 
x_43 = lean::box(x_39);
lean::cnstr_set(x_36, 0, x_43);
return x_36;
}
}
else
{
obj* x_44; uint8 x_45; uint8 x_46; 
x_44 = lean::cnstr_get(x_36, 1);
lean::inc(x_44);
lean::dec(x_36);
x_45 = 0;
x_46 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_45, x_11);
lean::dec(x_11);
if (x_46 == 0)
{
uint8 x_47; obj* x_48; obj* x_49; 
x_47 = 1;
x_48 = lean::box(x_47);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
return x_49;
}
else
{
obj* x_50; obj* x_51; 
x_50 = lean::box(x_45);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
}
}
else
{
uint8 x_52; 
lean::dec(x_11);
x_52 = !lean::is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_36, 0);
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_36);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_11);
x_56 = l_List_reverse___rarg(x_11);
x_57 = l_List_mfor___main___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__5(x_56, x_6);
if (lean::obj_tag(x_57) == 0)
{
uint8 x_58; 
x_58 = !lean::is_exclusive(x_57);
if (x_58 == 0)
{
obj* x_59; uint8 x_60; uint8 x_61; 
x_59 = lean::cnstr_get(x_57, 0);
lean::dec(x_59);
x_60 = 0;
x_61 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_60, x_11);
lean::dec(x_11);
if (x_61 == 0)
{
uint8 x_62; obj* x_63; 
x_62 = 1;
x_63 = lean::box(x_62);
lean::cnstr_set(x_57, 0, x_63);
return x_57;
}
else
{
obj* x_64; 
x_64 = lean::box(x_60);
lean::cnstr_set(x_57, 0, x_64);
return x_57;
}
}
else
{
obj* x_65; uint8 x_66; uint8 x_67; 
x_65 = lean::cnstr_get(x_57, 1);
lean::inc(x_65);
lean::dec(x_57);
x_66 = 0;
x_67 = l_List_foldr___main___at_Lean_MessageLog_hasErrors___spec__1(x_66, x_11);
lean::dec(x_11);
if (x_67 == 0)
{
uint8 x_68; obj* x_69; obj* x_70; 
x_68 = 1;
x_69 = lean::box(x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
return x_70;
}
else
{
obj* x_71; obj* x_72; 
x_71 = lean::box(x_66);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
}
}
else
{
uint8 x_73; 
lean::dec(x_11);
x_73 = !lean::is_exclusive(x_57);
if (x_73 == 0)
{
return x_57;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_57, 0);
x_75 = lean::cnstr_get(x_57, 1);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_57);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
obj* l___private_init_lean_parser_module_4__testModuleParserAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_3);
lean::dec(x_3);
x_8 = l___private_init_lean_parser_module_4__testModuleParserAux___main(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l___private_init_lean_parser_module_4__testModuleParserAux(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_module_4__testModuleParserAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_lean_parser_module_4__testModuleParserAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_3);
lean::dec(x_3);
x_8 = l___private_init_lean_parser_module_4__testModuleParserAux(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_Lean_Parser_testModuleParser___lambda__1(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_module_4__testModuleParserAux___main(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_testModuleParser___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" parser");
return x_1;
}
}
obj* _init_l_Lean_Parser_testModuleParser___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_pure___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
namespace lean {
obj* test_module_parser_core(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = l_Lean_Parser_testModuleParser___closed__1;
lean::inc(x_3);
x_7 = lean::string_append(x_3, x_6);
x_8 = l_Lean_Parser_mkParserContextCore(x_1, x_2, x_3);
lean::inc(x_8);
lean::inc(x_1);
x_9 = l_Lean_Parser_parseHeader(x_1, x_8);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_14 = lean::box(x_4);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_testModuleParser___lambda__1___boxed), 7, 5);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_8);
lean::closure_set(x_15, 2, x_14);
lean::closure_set(x_15, 3, x_12);
lean::closure_set(x_15, 4, x_13);
if (x_4 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_11);
x_16 = l_Lean_Parser_testModuleParser___closed__2;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_15);
x_18 = lean_io_timeit(lean::box(0), x_7, x_17, x_5);
lean::dec(x_7);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_15);
x_21 = lean_io_timeit(lean::box(0), x_7, x_20, x_5);
lean::dec(x_7);
return x_21;
}
}
}
}
obj* l_Lean_Parser_testModuleParser___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_3);
lean::dec(x_3);
x_9 = l_Lean_Parser_testModuleParser___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_9;
}
}
obj* l_Lean_Parser_testModuleParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = lean::test_module_parser_core(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_parseFileAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to parse file");
return x_1;
}
}
obj* l_Lean_Parser_parseFileAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_Lean_Parser_parseCommand___main(x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_12 = l_Lean_Parser_isEOI(x_9);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::array_push(x_5, x_9);
x_3 = x_10;
x_4 = x_11;
x_5 = x_13;
goto _start;
}
else
{
uint8 x_15; 
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_1);
x_15 = l_List_isEmpty___main___rarg(x_11);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_5);
x_16 = l_List_reverse___rarg(x_11);
x_17 = l_List_mfor___main___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__5(x_16, x_6);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::dec(x_19);
x_20 = l_Lean_Parser_parseFileAux___main___closed__1;
lean::cnstr_set_tag(x_17, 1);
lean::cnstr_set(x_17, 0, x_20);
return x_17;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
lean::dec(x_17);
x_22 = l_Lean_Parser_parseFileAux___main___closed__1;
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_17, 0);
x_26 = lean::cnstr_get(x_17, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_17);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8 x_28; 
lean::dec(x_11);
x_28 = !lean::is_exclusive(x_6);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_6, 0);
lean::dec(x_29);
x_30 = l_Lean_nullKind;
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_5);
x_32 = l_Lean_Syntax_updateLeading___rarg(x_31);
lean::cnstr_set(x_6, 0, x_32);
return x_6;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_6, 1);
lean::inc(x_33);
lean::dec(x_6);
x_34 = l_Lean_nullKind;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_5);
x_36 = l_Lean_Syntax_updateLeading___rarg(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_33);
return x_37;
}
}
}
}
}
obj* l_Lean_Parser_parseFileAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_parseFileAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_prim_read_text_file(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_parseFile(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_realpath(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = lean_io_prim_read_text_file(x_6, x_4);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_8, 0);
lean::cnstr_set(x_8, 0, x_7);
x_11 = l_Lean_Parser_mkParserContextCore(x_1, x_10, x_6);
lean::inc(x_11);
lean::inc(x_1);
x_12 = l_Lean_Parser_parseHeader(x_1, x_11);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::mk_array(x_17, x_14);
x_19 = l_Lean_Parser_parseFileAux___main(x_1, x_11, x_15, x_16, x_18, x_8);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_20 = lean::cnstr_get(x_8, 0);
x_21 = lean::cnstr_get(x_8, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_8);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_mkParserContextCore(x_1, x_20, x_6);
lean::inc(x_23);
lean::inc(x_1);
x_24 = l_Lean_Parser_parseHeader(x_1, x_23);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
lean::dec(x_24);
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::mk_array(x_29, x_26);
x_31 = l_Lean_Parser_parseFileAux___main(x_1, x_23, x_27, x_28, x_30, x_22);
return x_31;
}
}
else
{
uint8 x_32; 
lean::dec(x_6);
lean::dec(x_1);
x_32 = !lean::is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_8, 0);
x_34 = lean::cnstr_get(x_8, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_8);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_4, 0);
x_37 = lean::cnstr_get(x_4, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_4);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
x_40 = lean_io_prim_read_text_file(x_36, x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_43 = x_40;
} else {
 lean::dec_ref(x_40);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_42);
x_45 = l_Lean_Parser_mkParserContextCore(x_1, x_41, x_36);
lean::inc(x_45);
lean::inc(x_1);
x_46 = l_Lean_Parser_parseHeader(x_1, x_45);
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 0);
lean::inc(x_48);
lean::dec(x_46);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
x_51 = lean::mk_nat_obj(1u);
x_52 = lean::mk_array(x_51, x_48);
x_53 = l_Lean_Parser_parseFileAux___main(x_1, x_45, x_49, x_50, x_52, x_44);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_36);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_40, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_40, 1);
lean::inc(x_55);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_56 = x_40;
} else {
 lean::dec_ref(x_40);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8 x_58; 
lean::dec(x_1);
x_58 = !lean::is_exclusive(x_4);
if (x_58 == 0)
{
return x_4;
}
else
{
obj* x_59; obj* x_60; obj* x_61; 
x_59 = lean::cnstr_get(x_4, 0);
x_60 = lean::cnstr_get(x_4, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_4);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
}
}
}
obj* l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_readTextFile___at_Lean_Parser_parseFile___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_message(obj*);
obj* initialize_init_lean_parser_command(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_module(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_message(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_command(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__1);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__2);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__3);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__4);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__5);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__6);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__7);
l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8 = _init_l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8();
lean::mark_persistent(l_Lean_Parser_Module_prelude___elambda__1___rarg___closed__8);
l_Lean_Parser_Module_prelude___closed__1 = _init_l_Lean_Parser_Module_prelude___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_prelude___closed__1);
l_Lean_Parser_Module_prelude___closed__2 = _init_l_Lean_Parser_Module_prelude___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_prelude___closed__2);
l_Lean_Parser_Module_prelude___closed__3 = _init_l_Lean_Parser_Module_prelude___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_prelude___closed__3);
l_Lean_Parser_Module_prelude___closed__4 = _init_l_Lean_Parser_Module_prelude___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_prelude___closed__4);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean::mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_importPath___elambda__1___closed__1 = _init_l_Lean_Parser_Module_importPath___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_importPath___elambda__1___closed__1);
l_Lean_Parser_Module_importPath___elambda__1___closed__2 = _init_l_Lean_Parser_Module_importPath___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_importPath___elambda__1___closed__2);
l_Lean_Parser_Module_importPath___closed__1 = _init_l_Lean_Parser_Module_importPath___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_importPath___closed__1);
l_Lean_Parser_Module_importPath___closed__2 = _init_l_Lean_Parser_Module_importPath___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_importPath___closed__2);
l_Lean_Parser_Module_importPath___closed__3 = _init_l_Lean_Parser_Module_importPath___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_importPath___closed__3);
l_Lean_Parser_Module_importPath___closed__4 = _init_l_Lean_Parser_Module_importPath___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_importPath___closed__4);
l_Lean_Parser_Module_importPath___closed__5 = _init_l_Lean_Parser_Module_importPath___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_importPath___closed__5);
l_Lean_Parser_Module_importPath___closed__6 = _init_l_Lean_Parser_Module_importPath___closed__6();
lean::mark_persistent(l_Lean_Parser_Module_importPath___closed__6);
l_Lean_Parser_Module_importPath = _init_l_Lean_Parser_Module_importPath();
lean::mark_persistent(l_Lean_Parser_Module_importPath);
l_Lean_Parser_Module_import___elambda__1___closed__1 = _init_l_Lean_Parser_Module_import___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__1);
l_Lean_Parser_Module_import___elambda__1___closed__2 = _init_l_Lean_Parser_Module_import___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__2);
l_Lean_Parser_Module_import___elambda__1___closed__3 = _init_l_Lean_Parser_Module_import___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__3);
l_Lean_Parser_Module_import___elambda__1___closed__4 = _init_l_Lean_Parser_Module_import___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__4);
l_Lean_Parser_Module_import___elambda__1___closed__5 = _init_l_Lean_Parser_Module_import___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__5);
l_Lean_Parser_Module_import___elambda__1___closed__6 = _init_l_Lean_Parser_Module_import___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__6);
l_Lean_Parser_Module_import___elambda__1___closed__7 = _init_l_Lean_Parser_Module_import___elambda__1___closed__7();
lean::mark_persistent(l_Lean_Parser_Module_import___elambda__1___closed__7);
l_Lean_Parser_Module_import___closed__1 = _init_l_Lean_Parser_Module_import___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import___closed__1);
l_Lean_Parser_Module_import___closed__2 = _init_l_Lean_Parser_Module_import___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_import___closed__2);
l_Lean_Parser_Module_import___closed__3 = _init_l_Lean_Parser_Module_import___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_import___closed__3);
l_Lean_Parser_Module_import___closed__4 = _init_l_Lean_Parser_Module_import___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_import___closed__4);
l_Lean_Parser_Module_import___closed__5 = _init_l_Lean_Parser_Module_import___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_import___closed__5);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean::mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header___elambda__1___closed__1 = _init_l_Lean_Parser_Module_header___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__1);
l_Lean_Parser_Module_header___elambda__1___closed__2 = _init_l_Lean_Parser_Module_header___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_header___elambda__1___closed__2);
l_Lean_Parser_Module_header___closed__1 = _init_l_Lean_Parser_Module_header___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header___closed__1);
l_Lean_Parser_Module_header___closed__2 = _init_l_Lean_Parser_Module_header___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_header___closed__2);
l_Lean_Parser_Module_header___closed__3 = _init_l_Lean_Parser_Module_header___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_header___closed__3);
l_Lean_Parser_Module_header___closed__4 = _init_l_Lean_Parser_Module_header___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_header___closed__4);
l_Lean_Parser_Module_header___closed__5 = _init_l_Lean_Parser_Module_header___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_header___closed__5);
l_Lean_Parser_Module_header___closed__6 = _init_l_Lean_Parser_Module_header___closed__6();
lean::mark_persistent(l_Lean_Parser_Module_header___closed__6);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean::mark_persistent(l_Lean_Parser_Module_header);
l_Lean_Parser_ModuleParserState_inhabited___closed__1 = _init_l_Lean_Parser_ModuleParserState_inhabited___closed__1();
lean::mark_persistent(l_Lean_Parser_ModuleParserState_inhabited___closed__1);
l_Lean_Parser_ModuleParserState_inhabited = _init_l_Lean_Parser_ModuleParserState_inhabited();
lean::mark_persistent(l_Lean_Parser_ModuleParserState_inhabited);
l___private_init_lean_parser_module_2__mkEOI___closed__1 = _init_l___private_init_lean_parser_module_2__mkEOI___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_2__mkEOI___closed__1);
l___private_init_lean_parser_module_2__mkEOI___closed__2 = _init_l___private_init_lean_parser_module_2__mkEOI___closed__2();
lean::mark_persistent(l___private_init_lean_parser_module_2__mkEOI___closed__2);
l___private_init_lean_parser_module_2__mkEOI___closed__3 = _init_l___private_init_lean_parser_module_2__mkEOI___closed__3();
lean::mark_persistent(l___private_init_lean_parser_module_2__mkEOI___closed__3);
l_Lean_Parser_testModuleParser___closed__1 = _init_l_Lean_Parser_testModuleParser___closed__1();
lean::mark_persistent(l_Lean_Parser_testModuleParser___closed__1);
l_Lean_Parser_testModuleParser___closed__2 = _init_l_Lean_Parser_testModuleParser___closed__2();
lean::mark_persistent(l_Lean_Parser_testModuleParser___closed__2);
l_Lean_Parser_parseFileAux___main___closed__1 = _init_l_Lean_Parser_parseFileAux___main___closed__1();
lean::mark_persistent(l_Lean_Parser_parseFileAux___main___closed__1);
return w;
}
