// Lean compiler output
// Module: Lean.Parser
// Imports: Init Lean.Parser.Basic Lean.Parser.Level Lean.Parser.Term Lean.Parser.Tactic Lean.Parser.Command Lean.Parser.Module Lean.Parser.Syntax Lean.Parser.Do
#include <lean/lean.h>
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
extern lean_object* l_Lean_Parser_Command_structFields___elambda__1___closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11399____closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__2(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1;
lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__39;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5;
lean_object* l_Lean_Parser_lookahead(lean_object*);
extern lean_object* l_Lean_Parser_charLit;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__36;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19;
extern lean_object* l_Lean_Parser_ident;
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_rawNatLit___closed__8;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20;
extern lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_rawNatLit___closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__4(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7;
lean_object* l_Lean_Parser_withPosition(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11515____closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_leadingNode_formatter___closed__1;
lean_object* l_Lean_Parser_Term_scientific_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1;
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
extern lean_object* l_term___x24_______closed__8;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11675____closed__4;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1;
extern lean_object* l_Lean_Parser_Tactic_intro___closed__12;
extern lean_object* l_term___x24_______closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__8;
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
extern lean_object* l_termS_x21_____closed__6;
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1;
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object*);
extern lean_object* l_Lean_scientificLitKind___closed__2;
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29;
lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_parserAliasesRef;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11283____closed__4;
extern lean_object* l_Lean_Parser_Tactic_location___closed__4;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33;
extern lean_object* l_Lean_numLitKind___closed__2;
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq___closed__4;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__37;
extern lean_object* l_term_x5b___x2c_x5d___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__3;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__5;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11;
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3;
extern lean_object* l_Lean_Parser_instOrElseParser___closed__1;
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_numLit;
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18;
lean_object* l_Lean_Parser_Term_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__40;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17;
lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4_(lean_object*);
extern lean_object* l_Lean_Parser_instAndThenParser___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11167____closed__8;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34;
extern lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2508____closed__10;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__38;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__16;
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__6;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__32;
extern lean_object* l_Array_term_____x5b___x3a___x5d___closed__6;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__5(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1;
extern lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__8;
extern lean_object* l_Lean_Parser_instInhabitedParser___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31;
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__12;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__3(lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__11;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12;
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26;
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("element");
return x_1;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Parser_sepBy(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Parser_sepBy1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l_Lean_Parser_sepBy(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l_Lean_Parser_sepBy1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("space before");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1;
x_2 = l_Lean_Parser_checkWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_numLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLit;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__1;
x_2 = l_Lean_Parser_Term_type___elambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__1;
x_2 = l_Lean_Parser_Command_structFields___elambda__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_lookahead), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_atomic), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_many), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_many1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_optional), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__2), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__3), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instOrElseParser___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instAndThenParser___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__4), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__37;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__5), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__39;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_parserAliasesRef;
x_3 = l_term___x24_______closed__8;
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_term_____x5b___x3a___x5d___closed__6;
x_8 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5;
x_9 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_7, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_rawNatLit___closed__8;
x_12 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6;
x_13 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_11, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__8;
x_16 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7;
x_17 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_15, x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__12;
x_20 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8;
x_21 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_19, x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__16;
x_24 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9;
x_25 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_23, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_identKind___closed__2;
x_28 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10;
x_29 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_27, x_28, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Parser_Tactic_intro___closed__12;
x_32 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12;
x_33 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_31, x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Parser_Tactic_inductionAlts___closed__10;
x_36 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14;
x_37 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_35, x_36, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2508____closed__10;
x_40 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16;
x_41 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_39, x_40, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_term___x24_______closed__4;
x_44 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18;
x_45 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_43, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_myMacro____x40_Init_Notation___hyg_11283____closed__4;
x_48 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20;
x_49 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_47, x_48, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_myMacro____x40_Init_Notation___hyg_11167____closed__8;
x_52 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22;
x_53 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_51, x_52, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_myMacro____x40_Init_Notation___hyg_11675____closed__4;
x_56 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24;
x_57 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_55, x_56, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_11399____closed__4;
x_60 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26;
x_61 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_59, x_60, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Parser_Tactic_location___closed__4;
x_64 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28;
x_65 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_63, x_64, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_termS_x21_____closed__6;
x_68 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30;
x_69 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_67, x_68, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_term_x5b___x2c_x5d___closed__6;
x_72 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32;
x_73 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_71, x_72, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Parser_Tactic_inductionAlts___closed__8;
x_76 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34;
x_77 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_75, x_76, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_myMacro____x40_Init_Notation___hyg_11515____closed__6;
x_80 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35;
x_81 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_79, x_80, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_rawNatLit___closed__4;
x_84 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__36;
x_85 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_83, x_84, x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_953____closed__32;
x_88 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__38;
x_89 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_87, x_88, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_Parser_Tactic_rwRuleSeq___closed__4;
x_92 = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__40;
x_93 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_91, x_92, x_90);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_89, 0);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_89);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_85);
if (x_98 == 0)
{
return x_85;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_85, 0);
x_100 = lean_ctor_get(x_85, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_85);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_81);
if (x_102 == 0)
{
return x_81;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_81, 0);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_81);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_77);
if (x_106 == 0)
{
return x_77;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_77, 0);
x_108 = lean_ctor_get(x_77, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_77);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_73);
if (x_110 == 0)
{
return x_73;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_73, 0);
x_112 = lean_ctor_get(x_73, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_73);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_69);
if (x_114 == 0)
{
return x_69;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_69, 0);
x_116 = lean_ctor_get(x_69, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_69);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_65);
if (x_118 == 0)
{
return x_65;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_65, 0);
x_120 = lean_ctor_get(x_65, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_65);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_61);
if (x_122 == 0)
{
return x_61;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_61, 0);
x_124 = lean_ctor_get(x_61, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_61);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_57);
if (x_126 == 0)
{
return x_57;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_57, 0);
x_128 = lean_ctor_get(x_57, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_57);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_53);
if (x_130 == 0)
{
return x_53;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_53, 0);
x_132 = lean_ctor_get(x_53, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_53);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_49);
if (x_134 == 0)
{
return x_49;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_49, 0);
x_136 = lean_ctor_get(x_49, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_49);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_45);
if (x_138 == 0)
{
return x_45;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_45, 0);
x_140 = lean_ctor_get(x_45, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_45);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_41);
if (x_142 == 0)
{
return x_41;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_41, 0);
x_144 = lean_ctor_get(x_41, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_41);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_37);
if (x_146 == 0)
{
return x_37;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_37, 0);
x_148 = lean_ctor_get(x_37, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_37);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_33);
if (x_150 == 0)
{
return x_33;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_33, 0);
x_152 = lean_ctor_get(x_33, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_33);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_29);
if (x_154 == 0)
{
return x_29;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_29, 0);
x_156 = lean_ctor_get(x_29, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_29);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_25);
if (x_158 == 0)
{
return x_25;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_25, 0);
x_160 = lean_ctor_get(x_25, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_25);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_21);
if (x_162 == 0)
{
return x_21;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_21, 0);
x_164 = lean_ctor_get(x_21, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_21);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_17);
if (x_166 == 0)
{
return x_17;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_17, 0);
x_168 = lean_ctor_get(x_17, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_17);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_13);
if (x_170 == 0)
{
return x_13;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_13, 0);
x_172 = lean_ctor_get(x_13, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_13);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_9);
if (x_174 == 0)
{
return x_9;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_9, 0);
x_176 = lean_ctor_get(x_9, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_9);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_5);
if (x_178 == 0)
{
return x_5;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_5, 0);
x_180 = lean_ctor_get(x_5, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_5);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
lean_object* lean_mk_antiquot_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Parser_mkAntiquot_parenthesizer___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_parenthesizer(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_ident_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_num_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_numLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_scientific_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_scientificLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_char_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_charLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_str_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = l_Lean_strLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* lean_mk_antiquot_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_mkAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_formatter(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__11;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_ident_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_numLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_scientificLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_scientificLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__7;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_charLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_leadingNode_formatter___closed__1;
x_7 = l_Lean_initFn____x40_Lean_Parser_Extra___hyg_1076____closed__5;
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLit_formatter), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = l_Lean_strLitKind___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_Parser_Level(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
lean_object* initialize_Lean_Parser_Tactic(lean_object*);
lean_object* initialize_Lean_Parser_Command(lean_object*);
lean_object* initialize_Lean_Parser_Module(lean_object*);
lean_object* initialize_Lean_Parser_Syntax(lean_object*);
lean_object* initialize_Lean_Parser_Do(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____lambda__1___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__6);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__7);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__8);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__9);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__10);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__11);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__12);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__13);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__14);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__15);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__16);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__17);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__18);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__19);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__20);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__21);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__22);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__23);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__24);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__25);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__26);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__27);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__28);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__29);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__30);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__31);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__32);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__33);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__34);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__35);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__36 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__36();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__36);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__37 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__37();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__37);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__38 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__38();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__38);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__39 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__39();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__39);
l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__40 = _init_l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__40();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4____closed__40);
res = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
