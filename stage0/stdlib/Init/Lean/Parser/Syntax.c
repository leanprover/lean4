// Lean compiler output
// Module: Init.Lean.Parser.Syntax
// Imports: Init.Lean.Parser.Parser
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
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2;
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1;
lean_object* l_Lean_Parser_syntaxParser___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_regSyntaxParserAttribute___closed__2;
lean_object* l_Lean_Parser_regSyntaxParserAttribute___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_categoryParser(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_regSyntaxParserAttribute(lean_object*);
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3;
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr(lean_object*);
lean_object* l_Lean_Parser_syntaxParser(uint8_t, lean_object*);
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinSyntaxParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regBuiltinSyntaxParserAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = 0;
x_5 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_regSyntaxParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntaxParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_regSyntaxParserAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_regSyntaxParserAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_regSyntaxParserAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_regSyntaxParserAttribute___closed__2;
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_syntaxParser(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4;
x_4 = l_Lean_Parser_categoryParser(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_syntaxParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_syntaxParser(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Parser_Parser(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Syntax(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Parser_Parser(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__1);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__2);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__3);
l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4();
lean_mark_persistent(l_Lean_Parser_regBuiltinSyntaxParserAttr___closed__4);
res = l_Lean_Parser_regBuiltinSyntaxParserAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_regSyntaxParserAttribute___closed__1 = _init_l_Lean_Parser_regSyntaxParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_regSyntaxParserAttribute___closed__1);
l_Lean_Parser_regSyntaxParserAttribute___closed__2 = _init_l_Lean_Parser_regSyntaxParserAttribute___closed__2();
lean_mark_persistent(l_Lean_Parser_regSyntaxParserAttribute___closed__2);
res = l_Lean_Parser_regSyntaxParserAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
