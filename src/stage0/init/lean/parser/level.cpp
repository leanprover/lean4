// Lean compiler output
// Module: init.lean.parser.level
// Imports: init.lean.parser.parser
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
obj* l_Lean_Parser_levelParser___elambda__1___closed__1;
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
obj* l_Lean_Parser_builtinLevelParsingTable;
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_levelParser(obj*);
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj*);
obj* l_Lean_Parser_levelParser___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_levelParser___elambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinLevelParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("builtinLevelParsingTable");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_regBuiltinLevelParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__1;
x_3 = l_Lean_Parser_regBuiltinLevelParserAttr___closed__2;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_levelParser___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("universe level");
return x_1;
}
}
obj* l_Lean_Parser_levelParser___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_levelParser___elambda__1___closed__1;
x_6 = l_Lean_Parser_builtinLevelParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_levelParser(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser___elambda__1___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_Parser_inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_levelParser___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_levelParser___elambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* initialize_init_lean_parser_parser(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_level(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (io_result_is_error(w)) return w;
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinLevelParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinLevelParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinLevelParsingTable"), l_Lean_Parser_builtinLevelParsingTable);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__1);
l_Lean_Parser_regBuiltinLevelParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinLevelParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinLevelParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinLevelParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_levelParser___elambda__1___closed__1 = _init_l_Lean_Parser_levelParser___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_levelParser___elambda__1___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "levelParser"), 1, l_Lean_Parser_levelParser);
return w;
}
