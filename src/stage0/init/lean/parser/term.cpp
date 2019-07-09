// Lean compiler output
// Module: init.lean.parser.term
// Imports: init.lean.parser.parser init.lean.parser.level
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
obj* l___regBuiltinParser_Lean_Parser_Term_sub___closed__1;
obj* l_Lean_Parser_Term_arrow;
obj* l_Lean_Parser_Term_structInstSource;
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj*);
obj* l_Lean_Parser_termParser(uint8, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_ge___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_show___closed__1;
obj* l_Lean_Parser_orelseFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_strLitFn___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_match___closed__1;
obj* l_Lean_Parser_Term_num;
obj* l___regBuiltinParser_Lean_Parser_Term_nomatch___closed__1;
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_optType;
obj* l_Lean_Parser_Term_namedArgument;
obj* l_Lean_Parser_Term_array;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__2;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Term_unicodeInfixL(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_fromTerm;
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_list___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_add(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1;
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_forall(obj*);
obj* l_Lean_Parser_Term_infixR___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_le;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_lt___closed__1;
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Term_parenSpecial;
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_Term_and;
obj* l_Lean_Parser_Term_hole;
obj* l_Lean_Parser_termParserFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_have;
obj* l_Lean_Parser_Term_modN;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_if(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_fun(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp(obj*);
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_structInst___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
extern obj* l_Lean_Parser_builtinLevelParsingTable;
obj* l_Lean_Parser_builtinTermParsingTable;
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj*);
obj* l_Lean_Parser_Term_binderType___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1;
obj* l_Lean_Parser_Term_tupleTail;
obj* l___regBuiltinParser_Lean_Parser_Term_app___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_have___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_fun___closed__1;
obj* l_Lean_Parser_Term_infixR(obj*, obj*);
extern obj* l_Lean_Parser_appPrec;
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1;
obj* l_Lean_Parser_Term_binderTactic;
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_if___closed__1;
obj* l_Lean_Parser_Term_beq;
obj* l_Lean_Parser_Term_suffices;
obj* l_Lean_Parser_Term_implicitBinder(uint8);
obj* l_Lean_Parser_Term_sub;
obj* l_Lean_Parser_Term_mul;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___spec__2(uint8, uint8, obj*, obj*, obj*);
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___spec__2(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_termParserFn___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_or___closed__1;
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1;
obj* l_Lean_Parser_Term_implicitBinder___closed__2;
obj* l_Lean_Parser_Term_structInst;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___spec__3(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_infixL(obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__1;
obj* l_Lean_Parser_Term_str;
obj* l___regBuiltinParser_Lean_Parser_Term_modN(obj*);
obj* l_Lean_Parser_Term_equation;
obj* l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_id;
obj* l_Lean_Parser_Term_add;
obj* l_Lean_Parser_Term_haveAssign;
obj* l___regBuiltinParser_Lean_Parser_Term_proj(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj*);
obj* l_Lean_Parser_Term_depArrow;
obj* l___regBuiltinParser_Lean_Parser_Term_mul___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolNoWsFn___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_le(obj*);
obj* l_Lean_Parser_Term_fcomp;
obj* l_Lean_Parser_Term_unicodeInfixR___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_paren___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_proj___closed__1;
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_suffices(obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
obj* l_Lean_Parser_Term_binderIdent;
obj* l_Lean_Parser_Term_unicodeInfixR(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType(uint8);
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_eq(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_many1Fn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_array(obj*);
obj* l_Lean_Parser_Term_if;
obj* l___regBuiltinParser_Lean_Parser_Term_iff(obj*);
obj* l_Lean_Parser_termParserFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
obj* l_Lean_Parser_Term_iff;
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_type___closed__1;
obj* l_Lean_Parser_Term_simpleBinder;
obj* l_Lean_Parser_termParser___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_iff___closed__1;
obj* l_Lean_Parser_Term_bracktedBinder___closed__2;
obj* l_Lean_Parser_tryFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_cdot;
obj* l_Lean_Parser_Term_gt;
obj* l_Lean_Parser_Term_paren;
obj* l___regBuiltinParser_Lean_Parser_Term_modN___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sorry(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Term_sort;
obj* l_Lean_Parser_Term_infixL___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_hole___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_match(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_Lean_nullKind;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_sorry;
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_match;
extern obj* l_Lean_Parser_levelParserFn___rarg___closed__1;
obj* l_Lean_Parser_Term_explicitBinder___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___regBuiltinParser_Lean_Parser_Term_structInst(obj*);
obj* l_Lean_Parser_Term_unicodeInfixL___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_add___closed__1;
obj* l_Lean_Parser_Term_subtype;
obj* l_Lean_Parser_Term_forall;
obj* l___regBuiltinParser_Lean_Parser_Term_and(obj*);
obj* l_Lean_Parser_Term_mod;
obj* l___regBuiltinParser_Lean_Parser_Term_forall___closed__1;
obj* l_Lean_Parser_Term_proj;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_array___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_sub(obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_nomatch(obj*);
obj* l_Lean_Parser_Term_explicitBinder___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_and___closed__1;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_id___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_id(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_div(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mod___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj*);
obj* l_Lean_Parser_Term_unicodeInfixR___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___spec__3(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_id___closed__1;
obj* l_Lean_Parser_optionalFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_or;
obj* l_Lean_Parser_Term_binderDefault;
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_show;
obj* l_Lean_Parser_Term_explicitBinder(uint8);
obj* l_Lean_Parser_symbolNoWsInfo(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolCheckPrecFn___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_or(obj*);
obj* l_Lean_Parser_Term_instBinder;
obj* l___regBuiltinParser_Lean_Parser_Term_arrow(obj*);
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_structInst___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_le___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_have(obj*);
obj* l_Lean_Parser_Term_list;
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_eq___closed__1;
obj* l_Lean_Parser_Term_typeAscription;
obj* l_Lean_Parser_termParserFn(uint8);
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___spec__2(uint8, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_div___closed__1;
obj* l_Lean_Parser_identFn___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___spec__2(uint8, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj*);
obj* l_Lean_Parser_Term_implicitBinder___boxed(obj*);
obj* l_Lean_Parser_fieldIdx___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_bracktedBinder(uint8);
obj* l_Lean_Parser_Term_optIdent;
obj* l_Lean_Parser_nodeFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_show(obj*);
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_id___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1;
obj* l_Lean_Parser_termParserFn___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_beq(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_list(obj*);
obj* l_Lean_Parser_Term_explicitBinder___boxed(obj*);
obj* l_Lean_Parser_Term_nomatch;
obj* l___regBuiltinParser_Lean_Parser_Term_ge(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj*);
obj* l_Lean_Parser_unicodeSymbolInfo(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_type;
obj* l___regBuiltinParser_Lean_Parser_Term_subtype(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mod(obj*);
obj* l_Lean_Parser_Term_binderType___boxed(obj*);
obj* l_Lean_Parser_Term_anonymousCtor;
obj* l_Lean_Parser_Term_implicitBinder___closed__1;
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_Term_bracktedBinder___closed__1;
obj* l_Lean_Parser_Term_eq;
obj* l_Lean_Parser_Term_bracktedBinder___boxed(obj*);
obj* l_Lean_Parser_Term_structInstField;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_gt___closed__1;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_beq___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_gt(obj*);
obj* l_Lean_Parser_Term_div;
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_list___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_typeSpec;
obj* l_Lean_Parser_Term_ge;
obj* l___regBuiltinParser_Lean_Parser_Term_list___closed__1;
obj* l_Lean_Parser_Term_fun;
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mul(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepByInfo(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_lt(obj*);
obj* l_Lean_Parser_Term_lt;
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* l_Lean_Parser_Term_app;
obj* l___regBuiltinParser_Lean_Parser_Term_sort___closed__1;
obj* _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinTermParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("builtinTermParsingTable");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
x_3 = l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_termParserFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term");
return x_1;
}
}
obj* l_Lean_Parser_termParserFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_6 = l_Lean_Parser_builtinTermParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_termParserFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_termParserFn___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_termParserFn___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_termParserFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_termParserFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_termParser(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_termParser___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_termParser(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_Term_unicodeInfixR___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_Term_unicodeInfixR(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_String_trim(x_1);
x_6 = l_String_trim(x_2);
lean::inc(x_6);
lean::inc(x_5);
x_7 = l_Lean_Parser_unicodeSymbolInfo(x_5, x_6, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_3, x_9);
lean::dec(x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_Parser_inhabited___closed__1;
x_13 = l_Lean_Parser_andthenInfo(x_7, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_14, 0, x_8);
lean::closure_set(x_14, 1, x_11);
x_15 = l_Lean_Parser_epsilonInfo;
x_16 = l_Lean_Parser_andthenInfo(x_15, x_13);
x_17 = l_Lean_Parser_Term_unicodeInfixR___closed__1;
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_18, 0, x_17);
lean::closure_set(x_18, 1, x_14);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
obj* l_Lean_Parser_Term_unicodeInfixR___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_unicodeInfixR(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Term_infixR(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_2);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_String_trim(x_1);
lean::inc(x_4);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_6, 0, x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = l_Lean_Parser_Parser_inhabited___closed__1;
x_11 = l_Lean_Parser_andthenInfo(x_5, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_12, 0, x_6);
lean::closure_set(x_12, 1, x_9);
x_13 = l_Lean_Parser_epsilonInfo;
x_14 = l_Lean_Parser_andthenInfo(x_13, x_11);
x_15 = l_Lean_Parser_Term_unicodeInfixR___closed__1;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_15);
lean::closure_set(x_16, 1, x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Term_infixR___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_infixR(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Term_unicodeInfixL(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_String_trim(x_1);
x_6 = l_String_trim(x_2);
lean::inc(x_6);
lean::inc(x_5);
x_7 = l_Lean_Parser_unicodeSymbolInfo(x_5, x_6, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_9, 0, x_3);
x_10 = l_Lean_Parser_Parser_inhabited___closed__1;
x_11 = l_Lean_Parser_andthenInfo(x_7, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_9);
x_13 = l_Lean_Parser_epsilonInfo;
x_14 = l_Lean_Parser_andthenInfo(x_13, x_11);
x_15 = l_Lean_Parser_Term_unicodeInfixR___closed__1;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_15);
lean::closure_set(x_16, 1, x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Term_unicodeInfixL___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_unicodeInfixL(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Term_infixL(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::inc(x_2);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_String_trim(x_1);
lean::inc(x_4);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_6, 0, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_Lean_Parser_Parser_inhabited___closed__1;
x_9 = l_Lean_Parser_andthenInfo(x_5, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_10, 0, x_6);
lean::closure_set(x_10, 1, x_7);
x_11 = l_Lean_Parser_epsilonInfo;
x_12 = l_Lean_Parser_andthenInfo(x_11, x_9);
x_13 = l_Lean_Parser_Term_unicodeInfixR___closed__1;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_14, 0, x_13);
lean::closure_set(x_14, 1, x_10);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_Lean_Parser_Term_infixL___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(", ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(", ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinLevelParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_19 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1;
x_20 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2;
lean::inc(x_6);
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_6, x_14);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_18);
lean::dec(x_17);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_21;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
lean::dec(x_6);
x_24 = l_Lean_Parser_ParserState_restore(x_21, x_17, x_18);
lean::dec(x_17);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_3);
return x_26;
}
}
else
{
lean::dec(x_15);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
lean::dec(x_9);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_27);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_restore(x_14, x_9, x_10);
lean::dec(x_9);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_3);
return x_33;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___spec__2(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 0;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_id___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_id() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("id");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string("ident");
x_11 = l_Lean_Parser_mkAtomicInfo(x_10);
x_12 = 0;
x_13 = lean::box(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::box(0);
x_16 = lean::mk_string(".{");
x_17 = l_String_trim(x_16);
lean::dec(x_16);
lean::inc(x_17);
x_18 = l_Lean_Parser_symbolInfo(x_17, x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_21 = lean::box(1);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::mk_string(", ");
x_24 = l_String_trim(x_23);
lean::dec(x_23);
x_25 = l_Lean_Parser_symbolInfo(x_24, x_15);
x_26 = l_Lean_Parser_sepBy1Info(x_22, x_25);
x_27 = 0;
x_28 = lean::box(x_12);
x_29 = lean::box(x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_id___spec__1___boxed), 5, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::mk_string("}");
x_32 = l_String_trim(x_31);
lean::dec(x_31);
lean::inc(x_32);
x_33 = l_Lean_Parser_symbolInfo(x_32, x_15);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_34, 0, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_26, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_30);
lean::closure_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_andthenInfo(x_18, x_35);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_19);
lean::closure_set(x_38, 1, x_36);
x_39 = l_Lean_Parser_noFirstTokenInfo(x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_40, 0, x_38);
x_41 = l_Lean_Parser_andthenInfo(x_11, x_39);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_42, 0, x_14);
lean::closure_set(x_42, 1, x_40);
x_43 = l_Lean_Parser_nodeInfo(x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_44, 0, x_9);
lean::closure_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___spec__2(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_id___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_id___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_id___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("id");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_id(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_id___closed__1;
x_4 = l_Lean_Parser_Term_id;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_num() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("numLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numLitFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_num___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("num");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
x_4 = l_Lean_Parser_Term_num;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_str() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("strLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_strLitFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_str___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("str");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
x_4 = l_Lean_Parser_Term_str;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_type() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("type");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("Type");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_type___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("type");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_type___closed__1;
x_4 = l_Lean_Parser_Term_type;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sort() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sort");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("Sort");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_sort___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sort");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_sort___closed__1;
x_4 = l_Lean_Parser_Term_sort;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_hole() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("hole");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("_");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_hole___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("hole");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_hole___closed__1;
x_4 = l_Lean_Parser_Term_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sorry() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sorry");
lean::inc(x_8);
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_nodeInfo(x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sorry");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sorry(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1;
x_4 = l_Lean_Parser_Term_sorry;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_cdot() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("cdot");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("·");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("cdot");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1;
x_4 = l_Lean_Parser_Term_cdot;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_typeAscription() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("typeAscription");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" : ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___spec__3(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_19 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1;
x_20 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2;
lean::inc(x_6);
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_6, x_14);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_18);
lean::dec(x_17);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_21;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
lean::dec(x_6);
x_24 = l_Lean_Parser_ParserState_restore(x_21, x_17, x_18);
lean::dec(x_17);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_3);
return x_26;
}
}
else
{
lean::dec(x_15);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
lean::dec(x_9);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_27);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_restore(x_14, x_9, x_10);
lean::dec(x_9);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_3);
return x_33;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___spec__2(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 0;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___spec__3(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_tupleTail() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("tupleTail");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(", ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::inc(x_13);
x_18 = l_Lean_Parser_sepBy1Info(x_17, x_13);
x_19 = 0;
x_20 = 0;
x_21 = lean::box(x_19);
x_22 = lean::box(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1___boxed), 5, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_andthenInfo(x_13, x_18);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_14);
lean::closure_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_nodeInfo(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_9);
lean::closure_set(x_27, 1, x_25);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___spec__3(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___spec__2(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l_Lean_Parser_Term_parenSpecial() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = l_Lean_Parser_Term_tupleTail;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Term_typeAscription;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_noFirstTokenInfo(x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("(");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = l_Lean_Parser_Term_parenSpecial;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = l_Lean_Parser_andthenInfo(x_18, x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_20);
lean::closure_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_noFirstTokenInfo(x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_27, 0, x_25);
x_28 = lean::box(0);
x_29 = lean::mk_string(")");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = l_Lean_Parser_symbolInfo(x_30, x_28);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_32, 0, x_30);
x_33 = l_Lean_Parser_andthenInfo(x_26, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_34, 0, x_27);
lean::closure_set(x_34, 1, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_14, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_15);
lean::closure_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_nodeInfo(x_35);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_9);
lean::closure_set(x_38, 1, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_paren___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_paren___closed__1;
x_4 = l_Lean_Parser_Term_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_anonymousCtor() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("anonymousCtor");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("⟨");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(0);
x_20 = lean::mk_string(", ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_19);
x_23 = l_Lean_Parser_sepBy1Info(x_18, x_22);
x_24 = 0;
x_25 = 0;
x_26 = lean::box(x_24);
x_27 = lean::box(x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1___boxed), 5, 2);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_27);
x_29 = lean::mk_string("⟩");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = l_Lean_Parser_symbolInfo(x_30, x_19);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_32, 0, x_30);
x_33 = l_Lean_Parser_andthenInfo(x_23, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_34, 0, x_28);
lean::closure_set(x_34, 1, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_14, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_15);
lean::closure_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_nodeInfo(x_35);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_9);
lean::closure_set(x_38, 1, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("anonymousCtor");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1;
x_4 = l_Lean_Parser_Term_anonymousCtor;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_optIdent() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::box(0);
x_7 = lean::mk_string(" : ");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_9 = l_Lean_Parser_symbolInfo(x_8, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = l_Lean_Parser_andthenInfo(x_2, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_12, 0, x_5);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = l_Lean_Parser_noFirstTokenInfo(x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* _init_l_Lean_Parser_Term_if() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("if");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("if ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string(" then ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_23, 0, x_21);
x_24 = lean::mk_string(" else ");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_10);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_27, 0, x_25);
lean::inc(x_17);
x_28 = l_Lean_Parser_andthenInfo(x_26, x_17);
lean::inc(x_19);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_19);
lean::inc(x_17);
x_30 = l_Lean_Parser_andthenInfo(x_17, x_28);
lean::inc(x_19);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_31, 0, x_19);
lean::closure_set(x_31, 1, x_29);
x_32 = l_Lean_Parser_andthenInfo(x_22, x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_33, 0, x_23);
lean::closure_set(x_33, 1, x_31);
x_34 = l_Lean_Parser_andthenInfo(x_17, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_19);
lean::closure_set(x_35, 1, x_33);
x_36 = lean::mk_string("ident");
x_37 = l_Lean_Parser_mkAtomicInfo(x_36);
x_38 = 0;
x_39 = lean::box(x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_40, 0, x_39);
x_41 = lean::mk_string(" : ");
x_42 = l_String_trim(x_41);
lean::dec(x_41);
lean::inc(x_42);
x_43 = l_Lean_Parser_symbolInfo(x_42, x_10);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_44, 0, x_42);
x_45 = l_Lean_Parser_andthenInfo(x_37, x_43);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_46, 0, x_40);
lean::closure_set(x_46, 1, x_44);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_47, 0, x_46);
x_48 = l_Lean_Parser_noFirstTokenInfo(x_45);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_49, 0, x_47);
x_50 = l_Lean_Parser_andthenInfo(x_48, x_34);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_51, 0, x_49);
lean::closure_set(x_51, 1, x_35);
x_52 = l_Lean_Parser_andthenInfo(x_13, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_53, 0, x_14);
lean::closure_set(x_53, 1, x_51);
x_54 = l_Lean_Parser_nodeInfo(x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_55, 0, x_9);
lean::closure_set(x_55, 1, x_53);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_if___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("if");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_if(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_if___closed__1;
x_4 = l_Lean_Parser_Term_if;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_fromTerm() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("fromTerm");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" from ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l_Lean_Parser_Term_haveAssign() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("haveAssign");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" := ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l_Lean_Parser_Term_have() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("have");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("have ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_Term_haveAssign;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_22 = l_Lean_Parser_Term_fromTerm;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = l_Lean_Parser_orelseInfo(x_21, x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_22, 1);
lean::inc(x_26);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_25);
lean::closure_set(x_27, 1, x_26);
x_28 = lean::mk_string("; ");
x_29 = l_String_trim(x_28);
lean::dec(x_28);
lean::inc(x_29);
x_30 = l_Lean_Parser_symbolInfo(x_29, x_10);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_31, 0, x_29);
lean::inc(x_17);
x_32 = l_Lean_Parser_andthenInfo(x_30, x_17);
lean::inc(x_19);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_19);
x_34 = l_Lean_Parser_andthenInfo(x_24, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_27);
lean::closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_andthenInfo(x_17, x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_37, 0, x_19);
lean::closure_set(x_37, 1, x_35);
x_38 = lean::mk_string("ident");
x_39 = l_Lean_Parser_mkAtomicInfo(x_38);
x_40 = 0;
x_41 = lean::box(x_40);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_42, 0, x_41);
x_43 = lean::mk_string(" : ");
x_44 = l_String_trim(x_43);
lean::dec(x_43);
lean::inc(x_44);
x_45 = l_Lean_Parser_symbolInfo(x_44, x_10);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_46, 0, x_44);
x_47 = l_Lean_Parser_andthenInfo(x_39, x_45);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_48, 0, x_42);
lean::closure_set(x_48, 1, x_46);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_49, 0, x_48);
x_50 = l_Lean_Parser_noFirstTokenInfo(x_47);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_51, 0, x_49);
x_52 = l_Lean_Parser_andthenInfo(x_50, x_36);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_53, 0, x_51);
lean::closure_set(x_53, 1, x_37);
x_54 = l_Lean_Parser_andthenInfo(x_13, x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_55, 0, x_14);
lean::closure_set(x_55, 1, x_53);
x_56 = l_Lean_Parser_nodeInfo(x_54);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_57, 0, x_9);
lean::closure_set(x_57, 1, x_55);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_have___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("have");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_have(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_have___closed__1;
x_4 = l_Lean_Parser_Term_have;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_suffices() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("suffices");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("suffices ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string("; ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_23, 0, x_21);
lean::inc(x_17);
x_24 = l_Lean_Parser_andthenInfo(x_22, x_17);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_19);
x_26 = l_Lean_Parser_Term_fromTerm;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = l_Lean_Parser_andthenInfo(x_27, x_24);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_30, 0, x_29);
lean::closure_set(x_30, 1, x_25);
x_31 = l_Lean_Parser_andthenInfo(x_17, x_28);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_32, 0, x_19);
lean::closure_set(x_32, 1, x_30);
x_33 = lean::mk_string("ident");
x_34 = l_Lean_Parser_mkAtomicInfo(x_33);
x_35 = 0;
x_36 = lean::box(x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_37, 0, x_36);
x_38 = lean::mk_string(" : ");
x_39 = l_String_trim(x_38);
lean::dec(x_38);
lean::inc(x_39);
x_40 = l_Lean_Parser_symbolInfo(x_39, x_10);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_41, 0, x_39);
x_42 = l_Lean_Parser_andthenInfo(x_34, x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_37);
lean::closure_set(x_43, 1, x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_44, 0, x_43);
x_45 = l_Lean_Parser_noFirstTokenInfo(x_42);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_46, 0, x_44);
x_47 = l_Lean_Parser_andthenInfo(x_45, x_31);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_48, 0, x_46);
lean::closure_set(x_48, 1, x_32);
x_49 = l_Lean_Parser_andthenInfo(x_13, x_47);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_50, 0, x_14);
lean::closure_set(x_50, 1, x_48);
x_51 = l_Lean_Parser_nodeInfo(x_49);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_52, 0, x_9);
lean::closure_set(x_52, 1, x_50);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("suffices");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_suffices(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1;
x_4 = l_Lean_Parser_Term_suffices;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_show() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("show");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("show ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_Term_fromTerm;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_22 = l_Lean_Parser_andthenInfo(x_17, x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_24, 0, x_19);
lean::closure_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_andthenInfo(x_13, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_26, 0, x_14);
lean::closure_set(x_26, 1, x_24);
x_27 = l_Lean_Parser_nodeInfo(x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_28, 0, x_9);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_show___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("show");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_show(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_show___closed__1;
x_4 = l_Lean_Parser_Term_show;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_fun() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("fun");
lean::inc(x_8);
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("λ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
x_13 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_13);
lean::inc(x_12);
x_14 = l_Lean_Parser_unicodeSymbolInfo(x_12, x_13, x_10);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_appPrec;
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = 0;
x_22 = lean::box(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_20);
x_24 = lean::mk_string("⇒");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
x_26 = lean::mk_string("=>");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
lean::inc(x_25);
x_28 = l_Lean_Parser_unicodeSymbolInfo(x_25, x_27, x_10);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean::closure_set(x_29, 0, x_25);
lean::closure_set(x_29, 1, x_27);
x_30 = lean::mk_nat_obj(0u);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_31, 0, x_30);
lean::inc(x_18);
x_32 = l_Lean_Parser_andthenInfo(x_28, x_18);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_33, 0, x_29);
lean::closure_set(x_33, 1, x_31);
x_34 = l_Lean_Parser_andthenInfo(x_18, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_23);
lean::closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_andthenInfo(x_14, x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_37, 0, x_15);
lean::closure_set(x_37, 1, x_35);
x_38 = l_Lean_Parser_nodeInfo(x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_39, 0, x_9);
lean::closure_set(x_39, 1, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_fun___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("fun");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_fun(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_fun___closed__1;
x_4 = l_Lean_Parser_Term_fun;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_structInstField() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structInstField");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string("ident");
x_11 = l_Lean_Parser_mkAtomicInfo(x_10);
x_12 = 0;
x_13 = lean::box(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::box(0);
x_16 = lean::mk_string(" := ");
x_17 = l_String_trim(x_16);
lean::dec(x_16);
lean::inc(x_17);
x_18 = l_Lean_Parser_symbolInfo(x_17, x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_21 = lean::box(1);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::mk_nat_obj(0u);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = l_Lean_Parser_andthenInfo(x_18, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_26, 0, x_19);
lean::closure_set(x_26, 1, x_24);
x_27 = l_Lean_Parser_andthenInfo(x_11, x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_28, 0, x_14);
lean::closure_set(x_28, 1, x_26);
x_29 = l_Lean_Parser_nodeInfo(x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_30, 0, x_9);
lean::closure_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
obj* _init_l_Lean_Parser_Term_structInstSource() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structInstSource");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("..");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_noFirstTokenInfo(x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_21, 0, x_19);
x_22 = l_Lean_Parser_andthenInfo(x_13, x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_14);
lean::closure_set(x_23, 1, x_21);
x_24 = l_Lean_Parser_nodeInfo(x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_9);
lean::closure_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___spec__3(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_36; obj* x_37; 
x_8 = l_Lean_Parser_Term_structInstField;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = l_Lean_Parser_Term_structInstSource;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_13 = lean::array_get_size(x_12);
lean::dec(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::inc(x_6);
lean::inc(x_5);
x_36 = lean::apply_3(x_9, x_5, x_6, x_7);
x_37 = lean::cnstr_get(x_36, 3);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
lean::dec(x_11);
x_15 = x_36;
goto block_35;
}
else
{
obj* x_38; uint8 x_39; 
lean::dec(x_37);
x_38 = lean::cnstr_get(x_36, 1);
lean::inc(x_38);
x_39 = lean::nat_dec_eq(x_38, x_14);
lean::dec(x_38);
if (x_39 == 0)
{
lean::dec(x_11);
x_15 = x_36;
goto block_35;
}
else
{
obj* x_40; obj* x_41; 
lean::inc(x_14);
x_40 = l_Lean_Parser_ParserState_restore(x_36, x_13, x_14);
lean::inc(x_6);
lean::inc(x_5);
x_41 = lean::apply_3(x_11, x_5, x_6, x_40);
x_15 = x_41;
goto block_35;
}
}
block_35:
{
obj* x_16; 
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_14);
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_20 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1;
x_21 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2;
lean::inc(x_6);
x_22 = l_Lean_Parser_symbolFnAux(x_20, x_21, x_6, x_15);
x_23 = lean::cnstr_get(x_22, 3);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
lean::dec(x_19);
lean::dec(x_18);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_22;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_23);
lean::dec(x_6);
lean::dec(x_5);
x_25 = l_Lean_Parser_ParserState_restore(x_22, x_18, x_19);
lean::dec(x_18);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_3);
return x_27;
}
}
else
{
lean::dec(x_16);
lean::dec(x_6);
lean::dec(x_5);
if (x_4 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_14);
lean::dec(x_13);
x_28 = lean::box(0);
x_29 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_28);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_3);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = l_Lean_Parser_ParserState_restore(x_15, x_13, x_14);
lean::dec(x_13);
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_32, x_33, x_3);
return x_34;
}
}
}
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___spec__2(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 1;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___spec__3(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_structInst___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_structInst() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structInst");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("{");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::mk_string("ident");
x_17 = l_Lean_Parser_mkAtomicInfo(x_16);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::box(0);
x_22 = lean::mk_string(" . ");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_24 = l_Lean_Parser_symbolInfo(x_23, x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_25, 0, x_23);
x_26 = l_Lean_Parser_andthenInfo(x_17, x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_20);
lean::closure_set(x_27, 1, x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = l_Lean_Parser_noFirstTokenInfo(x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = l_Lean_Parser_Term_structInstField;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = l_Lean_Parser_Term_structInstSource;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = l_Lean_Parser_orelseInfo(x_32, x_34);
x_36 = lean::mk_string(", ");
x_37 = l_String_trim(x_36);
lean::dec(x_36);
x_38 = l_Lean_Parser_symbolInfo(x_37, x_21);
x_39 = l_Lean_Parser_sepByInfo(x_35, x_38);
x_40 = 1;
x_41 = lean::box(x_18);
x_42 = lean::box(x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepByFn___at_Lean_Parser_Term_structInst___spec__1___boxed), 5, 2);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_42);
x_44 = lean::mk_string("}");
x_45 = l_String_trim(x_44);
lean::dec(x_44);
lean::inc(x_45);
x_46 = l_Lean_Parser_symbolInfo(x_45, x_21);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_47, 0, x_45);
x_48 = l_Lean_Parser_andthenInfo(x_39, x_46);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_49, 0, x_43);
lean::closure_set(x_49, 1, x_47);
x_50 = l_Lean_Parser_andthenInfo(x_29, x_48);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_51, 0, x_30);
lean::closure_set(x_51, 1, x_49);
x_52 = l_Lean_Parser_andthenInfo(x_14, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_53, 0, x_15);
lean::closure_set(x_53, 1, x_51);
x_54 = l_Lean_Parser_nodeInfo(x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_55, 0, x_9);
lean::closure_set(x_55, 1, x_53);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___spec__3(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
return x_11;
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___spec__2(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_structInst___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepByFn___at_Lean_Parser_Term_structInst___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structInst");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_structInst(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1;
x_4 = l_Lean_Parser_Term_structInst;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_typeSpec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("typeSpec");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" : ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l_Lean_Parser_Term_optType() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_Parser_Term_typeSpec;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_subtype() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("subtype");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("{");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::mk_string("ident");
x_16 = l_Lean_Parser_mkAtomicInfo(x_15);
x_17 = 0;
x_18 = lean::box(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string(" // ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_23, 0, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_25 = lean::box(1);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::mk_string("}");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = l_Lean_Parser_symbolInfo(x_30, x_10);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_32, 0, x_30);
x_33 = l_Lean_Parser_andthenInfo(x_26, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_34, 0, x_28);
lean::closure_set(x_34, 1, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_22, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_23);
lean::closure_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_Term_optType;
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_39 = l_Lean_Parser_andthenInfo(x_38, x_35);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_41, 0, x_40);
lean::closure_set(x_41, 1, x_36);
x_42 = l_Lean_Parser_andthenInfo(x_16, x_39);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_19);
lean::closure_set(x_43, 1, x_41);
x_44 = l_Lean_Parser_andthenInfo(x_13, x_42);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_45, 0, x_14);
lean::closure_set(x_45, 1, x_43);
x_46 = l_Lean_Parser_nodeInfo(x_44);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_47, 0, x_9);
lean::closure_set(x_47, 1, x_45);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("subtype");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_subtype(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1;
x_4 = l_Lean_Parser_Term_subtype;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(",");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(",");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("'");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_19 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__1;
x_20 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__2;
lean::inc(x_6);
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_6, x_14);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_18);
lean::dec(x_17);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_21;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
lean::dec(x_6);
x_24 = l_Lean_Parser_ParserState_restore(x_21, x_17, x_18);
lean::dec(x_17);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_3);
return x_26;
}
}
else
{
lean::dec(x_15);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
lean::dec(x_9);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_27);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_restore(x_14, x_9, x_10);
lean::dec(x_9);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_3);
return x_33;
}
}
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___spec__2(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 1;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_list___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_list() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("list");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::mk_string("[");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(0);
x_20 = lean::mk_string(",");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_19);
x_23 = l_Lean_Parser_sepByInfo(x_18, x_22);
x_24 = 0;
x_25 = 1;
x_26 = lean::box(x_24);
x_27 = lean::box(x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepByFn___at_Lean_Parser_Term_list___spec__1___boxed), 5, 2);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_27);
x_29 = lean::mk_string("]");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = l_Lean_Parser_symbolInfo(x_30, x_19);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_32, 0, x_30);
x_33 = l_Lean_Parser_andthenInfo(x_23, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_34, 0, x_28);
lean::closure_set(x_34, 1, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_14, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_15);
lean::closure_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_nodeInfo(x_35);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_9);
lean::closure_set(x_38, 1, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___spec__2(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_sepByFn___at_Lean_Parser_Term_list___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepByFn___at_Lean_Parser_Term_list___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_list___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("list");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_list(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_list___closed__1;
x_4 = l_Lean_Parser_Term_list;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_binderIdent() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_Term_hole;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = l_Lean_Parser_orelseInfo(x_2, x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_binderType___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
lean::inc(x_3);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = l_Lean_Parser_andthenInfo(x_4, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_12, 0, x_5);
lean::closure_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_noFirstTokenInfo(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* _init_l_Lean_Parser_Term_binderType___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
lean::inc(x_3);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = l_Lean_Parser_andthenInfo(x_4, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_12, 0, x_5);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_Term_binderType(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_binderType___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_binderType___closed__2;
return x_3;
}
}
}
obj* l_Lean_Parser_Term_binderType___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_Term_binderType(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Term_binderDefault() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("binderDefault");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" := ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l_Lean_Parser_Term_binderTactic() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("binderTactic");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" . ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("explicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("(");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_Term_binderIdent;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_17);
x_21 = l_Lean_Parser_Term_binderDefault;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = l_Lean_Parser_Term_binderTactic;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = l_Lean_Parser_orelseInfo(x_22, x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_noFirstTokenInfo(x_25);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = lean::mk_string(")");
x_32 = l_String_trim(x_31);
lean::dec(x_31);
lean::inc(x_32);
x_33 = l_Lean_Parser_symbolInfo(x_32, x_10);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_34, 0, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_29, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_30);
lean::closure_set(x_36, 1, x_34);
x_37 = lean::mk_string(" : ");
x_38 = l_String_trim(x_37);
lean::dec(x_37);
lean::inc(x_38);
x_39 = l_Lean_Parser_symbolInfo(x_38, x_10);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_40, 0, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_42 = lean::box(1);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::mk_nat_obj(0u);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_45, 0, x_44);
x_46 = l_Lean_Parser_andthenInfo(x_39, x_43);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_47, 0, x_40);
lean::closure_set(x_47, 1, x_45);
x_48 = l_Lean_Parser_noFirstTokenInfo(x_46);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_49, 0, x_47);
x_50 = l_Lean_Parser_andthenInfo(x_48, x_35);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_51, 0, x_49);
lean::closure_set(x_51, 1, x_36);
x_52 = l_Lean_Parser_andthenInfo(x_16, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_53, 0, x_20);
lean::closure_set(x_53, 1, x_51);
x_54 = l_Lean_Parser_andthenInfo(x_13, x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_55, 0, x_14);
lean::closure_set(x_55, 1, x_53);
x_56 = l_Lean_Parser_nodeInfo(x_54);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_57, 0, x_9);
lean::closure_set(x_57, 1, x_55);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("explicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("(");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_Term_binderIdent;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_17);
x_21 = l_Lean_Parser_Term_binderDefault;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = l_Lean_Parser_Term_binderTactic;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = l_Lean_Parser_orelseInfo(x_22, x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_noFirstTokenInfo(x_25);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = lean::mk_string(")");
x_32 = l_String_trim(x_31);
lean::dec(x_31);
lean::inc(x_32);
x_33 = l_Lean_Parser_symbolInfo(x_32, x_10);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_34, 0, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_29, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_30);
lean::closure_set(x_36, 1, x_34);
x_37 = lean::mk_string(" : ");
x_38 = l_String_trim(x_37);
lean::dec(x_37);
lean::inc(x_38);
x_39 = l_Lean_Parser_symbolInfo(x_38, x_10);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_40, 0, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_42 = lean::box(1);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::mk_nat_obj(0u);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_45, 0, x_44);
x_46 = l_Lean_Parser_andthenInfo(x_39, x_43);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_47, 0, x_40);
lean::closure_set(x_47, 1, x_45);
x_48 = l_Lean_Parser_andthenInfo(x_46, x_35);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_49, 0, x_47);
lean::closure_set(x_49, 1, x_36);
x_50 = l_Lean_Parser_andthenInfo(x_16, x_48);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_51, 0, x_20);
lean::closure_set(x_51, 1, x_49);
x_52 = l_Lean_Parser_andthenInfo(x_13, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_53, 0, x_14);
lean::closure_set(x_53, 1, x_51);
x_54 = l_Lean_Parser_nodeInfo(x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_55, 0, x_9);
lean::closure_set(x_55, 1, x_53);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
obj* l_Lean_Parser_Term_explicitBinder(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_explicitBinder___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_explicitBinder___closed__2;
return x_3;
}
}
}
obj* l_Lean_Parser_Term_explicitBinder___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_Term_explicitBinder(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("implicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("{");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_Term_binderIdent;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_17);
x_21 = lean::mk_string("}");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = lean::mk_string(" : ");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_27 = l_Lean_Parser_symbolInfo(x_26, x_10);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_28, 0, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_30 = lean::box(1);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_nat_obj(0u);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_33, 0, x_32);
x_34 = l_Lean_Parser_andthenInfo(x_27, x_31);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_28);
lean::closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_noFirstTokenInfo(x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_37, 0, x_35);
x_38 = l_Lean_Parser_andthenInfo(x_36, x_23);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_24);
x_40 = l_Lean_Parser_andthenInfo(x_16, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_41, 0, x_20);
lean::closure_set(x_41, 1, x_39);
x_42 = l_Lean_Parser_andthenInfo(x_13, x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_14);
lean::closure_set(x_43, 1, x_41);
x_44 = l_Lean_Parser_nodeInfo(x_42);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_45, 0, x_9);
lean::closure_set(x_45, 1, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("implicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("{");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = l_Lean_Parser_Term_binderIdent;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_17);
x_21 = lean::mk_string("}");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = lean::mk_string(" : ");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_27 = l_Lean_Parser_symbolInfo(x_26, x_10);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_28, 0, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_30 = lean::box(1);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_nat_obj(0u);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_33, 0, x_32);
x_34 = l_Lean_Parser_andthenInfo(x_27, x_31);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_28);
lean::closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_andthenInfo(x_34, x_23);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_37, 0, x_35);
lean::closure_set(x_37, 1, x_24);
x_38 = l_Lean_Parser_andthenInfo(x_16, x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_39, 0, x_20);
lean::closure_set(x_39, 1, x_37);
x_40 = l_Lean_Parser_andthenInfo(x_13, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_41, 0, x_14);
lean::closure_set(x_41, 1, x_39);
x_42 = l_Lean_Parser_nodeInfo(x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_9);
lean::closure_set(x_43, 1, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
obj* l_Lean_Parser_Term_implicitBinder(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_implicitBinder___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_implicitBinder___closed__2;
return x_3;
}
}
}
obj* l_Lean_Parser_Term_implicitBinder___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_Term_implicitBinder(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Term_instBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("instBinder");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("[");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string("]");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_23, 0, x_21);
x_24 = l_Lean_Parser_andthenInfo(x_17, x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_19);
lean::closure_set(x_25, 1, x_23);
x_26 = lean::mk_string("ident");
x_27 = l_Lean_Parser_mkAtomicInfo(x_26);
x_28 = 0;
x_29 = lean::box(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::mk_string(" : ");
x_32 = l_String_trim(x_31);
lean::dec(x_31);
lean::inc(x_32);
x_33 = l_Lean_Parser_symbolInfo(x_32, x_10);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_34, 0, x_32);
x_35 = l_Lean_Parser_andthenInfo(x_27, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_30);
lean::closure_set(x_36, 1, x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_37, 0, x_36);
x_38 = l_Lean_Parser_noFirstTokenInfo(x_35);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_39, 0, x_37);
x_40 = l_Lean_Parser_andthenInfo(x_38, x_24);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_41, 0, x_39);
lean::closure_set(x_41, 1, x_25);
x_42 = l_Lean_Parser_andthenInfo(x_13, x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_14);
lean::closure_set(x_43, 1, x_41);
x_44 = l_Lean_Parser_nodeInfo(x_42);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_45, 0, x_9);
lean::closure_set(x_45, 1, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
obj* _init_l_Lean_Parser_Term_bracktedBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_instBinder;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_bracktedBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_instBinder;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_Term_bracktedBinder(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = l_Lean_Parser_Term_explicitBinder(x_1);
x_3 = l_Lean_Parser_Term_implicitBinder(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_Term_bracktedBinder___closed__1;
x_6 = l_Lean_Parser_orelseInfo(x_4, x_5);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = l_Lean_Parser_Term_bracktedBinder___closed__2;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = l_Lean_Parser_orelseInfo(x_10, x_6);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_13, 0, x_12);
lean::closure_set(x_13, 1, x_9);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_Lean_Parser_Term_bracktedBinder___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_Term_bracktedBinder(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Term_depArrow() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("depArrow");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = 1;
x_11 = l_Lean_Parser_Term_bracktedBinder(x_10);
x_12 = lean::mk_string(" → ");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = lean::mk_string(" -> ");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
x_16 = lean::mk_nat_obj(25u);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::inc(x_15);
lean::inc(x_13);
x_18 = l_Lean_Parser_unicodeSymbolInfo(x_13, x_15, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolCheckPrecFn___boxed), 6, 3);
lean::closure_set(x_19, 0, x_13);
lean::closure_set(x_19, 1, x_15);
lean::closure_set(x_19, 2, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_21 = lean::box(1);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::mk_nat_obj(0u);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = l_Lean_Parser_andthenInfo(x_18, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_26, 0, x_19);
lean::closure_set(x_26, 1, x_24);
x_27 = lean::cnstr_get(x_11, 0);
lean::inc(x_27);
x_28 = l_Lean_Parser_andthenInfo(x_27, x_25);
x_29 = lean::cnstr_get(x_11, 1);
lean::inc(x_29);
lean::dec(x_11);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_30, 0, x_29);
lean::closure_set(x_30, 1, x_26);
x_31 = l_Lean_Parser_nodeInfo(x_28);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_32, 0, x_9);
lean::closure_set(x_32, 1, x_30);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("depArrow");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1;
x_4 = l_Lean_Parser_Term_depArrow;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_simpleBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("simpleBinder");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_Term_binderIdent;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_13 = 0;
x_14 = lean::box(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_15, 0, x_14);
lean::closure_set(x_15, 1, x_12);
x_16 = l_Lean_Parser_nodeInfo(x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l_Lean_Parser_Term_forall() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("forall");
lean::inc(x_8);
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("∀");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
x_13 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_13);
lean::inc(x_12);
x_14 = l_Lean_Parser_unicodeSymbolInfo(x_12, x_13, x_10);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_13);
x_16 = 0;
x_17 = l_Lean_Parser_Term_bracktedBinder(x_16);
x_18 = l_Lean_Parser_Term_simpleBinder;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
x_21 = l_Lean_Parser_orelseInfo(x_19, x_20);
x_22 = lean::cnstr_get(x_18, 1);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
lean::dec(x_17);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_24, 0, x_22);
lean::closure_set(x_24, 1, x_23);
x_25 = 0;
x_26 = lean::box(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_24);
x_28 = lean::mk_string(", ");
x_29 = l_String_trim(x_28);
lean::dec(x_28);
lean::inc(x_29);
x_30 = l_Lean_Parser_symbolInfo(x_29, x_10);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_31, 0, x_29);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_33 = lean::box(1);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::mk_nat_obj(0u);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_36, 0, x_35);
x_37 = l_Lean_Parser_andthenInfo(x_30, x_34);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_31);
lean::closure_set(x_38, 1, x_36);
x_39 = l_Lean_Parser_andthenInfo(x_21, x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_40, 0, x_27);
lean::closure_set(x_40, 1, x_38);
x_41 = l_Lean_Parser_andthenInfo(x_14, x_39);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_42, 0, x_15);
lean::closure_set(x_42, 1, x_40);
x_43 = l_Lean_Parser_nodeInfo(x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_44, 0, x_9);
lean::closure_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_forall___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("forall");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_forall(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_forall___closed__1;
x_4 = l_Lean_Parser_Term_forall;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_equation() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("equation");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(" | ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string(", ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
lean::inc(x_17);
x_23 = l_Lean_Parser_sepBy1Info(x_17, x_22);
x_24 = 0;
x_25 = 0;
x_26 = lean::box(x_24);
x_27 = lean::box(x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1___boxed), 5, 2);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_27);
x_29 = lean::mk_string(" => ");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = l_Lean_Parser_symbolInfo(x_30, x_10);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_32, 0, x_30);
x_33 = l_Lean_Parser_andthenInfo(x_31, x_17);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_19);
x_35 = l_Lean_Parser_andthenInfo(x_23, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_36, 0, x_28);
lean::closure_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_andthenInfo(x_13, x_35);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_38, 0, x_14);
lean::closure_set(x_38, 1, x_36);
x_39 = l_Lean_Parser_nodeInfo(x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_40, 0, x_9);
lean::closure_set(x_40, 1, x_38);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
obj* _init_l_Lean_Parser_Term_match() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("match");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("match ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_string(", ");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
x_20 = l_Lean_Parser_symbolInfo(x_19, x_10);
x_21 = l_Lean_Parser_sepBy1Info(x_17, x_20);
x_22 = 0;
x_23 = 0;
x_24 = lean::box(x_22);
x_25 = lean::box(x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Term_tupleTail___spec__1___boxed), 5, 2);
lean::closure_set(x_26, 0, x_24);
lean::closure_set(x_26, 1, x_25);
x_27 = lean::mk_string(" with ");
x_28 = l_String_trim(x_27);
lean::dec(x_27);
lean::inc(x_28);
x_29 = l_Lean_Parser_symbolInfo(x_28, x_10);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = l_Lean_Parser_Term_equation;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
x_34 = lean::box(x_22);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean::closure_set(x_35, 0, x_34);
lean::closure_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_andthenInfo(x_29, x_32);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_37, 0, x_30);
lean::closure_set(x_37, 1, x_35);
x_38 = l_Lean_Parser_Term_optType;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = l_Lean_Parser_andthenInfo(x_39, x_36);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_42, 0, x_41);
lean::closure_set(x_42, 1, x_37);
x_43 = l_Lean_Parser_andthenInfo(x_21, x_40);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_44, 0, x_26);
lean::closure_set(x_44, 1, x_42);
x_45 = l_Lean_Parser_andthenInfo(x_13, x_43);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_46, 0, x_14);
lean::closure_set(x_46, 1, x_44);
x_47 = l_Lean_Parser_nodeInfo(x_45);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_48, 0, x_9);
lean::closure_set(x_48, 1, x_46);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_match___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("match");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_match(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_match___closed__1;
x_4 = l_Lean_Parser_Term_match;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_nomatch() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("nomatch");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("nomatch ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_21, 0, x_14);
lean::closure_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_nomatch___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("nomatch");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_nomatch(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_nomatch___closed__1;
x_4 = l_Lean_Parser_Term_nomatch;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_namedArgument() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("namedArgument");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("(");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_12);
x_15 = lean::mk_string("ident");
x_16 = l_Lean_Parser_mkAtomicInfo(x_15);
x_17 = 1;
x_18 = lean::box(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string(" := ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_23, 0, x_21);
x_24 = l_Lean_Parser_andthenInfo(x_16, x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_19);
lean::closure_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_andthenInfo(x_13, x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_14);
lean::closure_set(x_27, 1, x_25);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_30 = lean::box(1);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_nat_obj(0u);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_33, 0, x_32);
x_34 = lean::mk_string(")");
x_35 = l_String_trim(x_34);
lean::dec(x_34);
lean::inc(x_35);
x_36 = l_Lean_Parser_symbolInfo(x_35, x_10);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_37, 0, x_35);
x_38 = l_Lean_Parser_andthenInfo(x_31, x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_39, 0, x_33);
lean::closure_set(x_39, 1, x_37);
x_40 = l_Lean_Parser_andthenInfo(x_26, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_41, 0, x_28);
lean::closure_set(x_41, 1, x_39);
x_42 = l_Lean_Parser_nodeInfo(x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_43, 0, x_9);
lean::closure_set(x_43, 1, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
obj* _init_l_Lean_Parser_Term_app() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("app");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_11 = lean::box(1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_appPrec;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = l_Lean_Parser_Term_namedArgument;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = l_Lean_Parser_orelseInfo(x_16, x_12);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_14);
x_20 = l_Lean_Parser_epsilonInfo;
x_21 = l_Lean_Parser_andthenInfo(x_20, x_17);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_19);
x_24 = l_Lean_Parser_nodeInfo(x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_25, 0, x_9);
lean::closure_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_app___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("app");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_app___closed__1;
x_4 = l_Lean_Parser_Term_app;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_proj() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("proj");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_10, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::mk_string(".");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = l_Lean_Parser_symbolNoWsInfo(x_15, x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolNoWsFn___boxed), 4, 1);
lean::closure_set(x_17, 0, x_15);
x_18 = lean::mk_string("fieldIdx");
x_19 = l_Lean_Parser_mkAtomicInfo(x_18);
x_20 = lean::mk_string("ident");
x_21 = l_Lean_Parser_mkAtomicInfo(x_20);
x_22 = 1;
x_23 = lean::box(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = l_Lean_Parser_orelseInfo(x_19, x_21);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_fieldIdx___lambda__1___boxed), 3, 0);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_24);
x_28 = l_Lean_Parser_andthenInfo(x_16, x_25);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_29, 0, x_17);
lean::closure_set(x_29, 1, x_27);
x_30 = l_Lean_Parser_epsilonInfo;
x_31 = l_Lean_Parser_andthenInfo(x_30, x_28);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_33, 0, x_32);
lean::closure_set(x_33, 1, x_29);
x_34 = l_Lean_Parser_nodeInfo(x_31);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_9);
lean::closure_set(x_35, 1, x_33);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_proj___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("proj");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_proj(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_proj___closed__1;
x_4 = l_Lean_Parser_Term_proj;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_arrow() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("arrow");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" → ");
x_11 = lean::mk_string(" -> ");
x_12 = lean::mk_nat_obj(25u);
x_13 = l_Lean_Parser_Term_unicodeInfixR(x_10, x_11, x_12);
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("arrow");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_arrow(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1;
x_4 = l_Lean_Parser_Term_arrow;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_array() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("array");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = l_Lean_Parser_appPrec;
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_10, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::mk_string("[");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = l_Lean_Parser_symbolNoWsInfo(x_15, x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolNoWsFn___boxed), 4, 1);
lean::closure_set(x_17, 0, x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_19 = lean::box(1);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::box(0);
x_24 = lean::mk_string("]");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_27, 0, x_25);
x_28 = l_Lean_Parser_andthenInfo(x_20, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_29, 0, x_22);
lean::closure_set(x_29, 1, x_27);
x_30 = l_Lean_Parser_andthenInfo(x_16, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_31, 0, x_17);
lean::closure_set(x_31, 1, x_29);
x_32 = l_Lean_Parser_epsilonInfo;
x_33 = l_Lean_Parser_andthenInfo(x_32, x_30);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_35, 0, x_34);
lean::closure_set(x_35, 1, x_31);
x_36 = l_Lean_Parser_nodeInfo(x_33);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_37, 0, x_9);
lean::closure_set(x_37, 1, x_35);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_array___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("array");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_array(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_array___closed__1;
x_4 = l_Lean_Parser_Term_array;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_fcomp() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("fcomp");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" ∘ ");
x_11 = lean::mk_nat_obj(90u);
x_12 = l_Lean_Parser_Term_infixR(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("fcomp");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1;
x_4 = l_Lean_Parser_Term_fcomp;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_add() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("add");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" + ");
x_11 = lean::mk_nat_obj(65u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_add___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("add");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_add(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_add___closed__1;
x_4 = l_Lean_Parser_Term_add;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sub() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sub");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" - ");
x_11 = lean::mk_nat_obj(65u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_sub___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("sub");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sub(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_sub___closed__1;
x_4 = l_Lean_Parser_Term_sub;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_mul() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("mul");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" * ");
x_11 = lean::mk_nat_obj(70u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_mul___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("mul");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_mul(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_mul___closed__1;
x_4 = l_Lean_Parser_Term_mul;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_div() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("div");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" / ");
x_11 = lean::mk_nat_obj(70u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_div___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("div");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_div(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_div___closed__1;
x_4 = l_Lean_Parser_Term_div;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_mod() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("mod");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" % ");
x_11 = lean::mk_nat_obj(70u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_mod___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("mod");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_mod(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_mod___closed__1;
x_4 = l_Lean_Parser_Term_mod;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_modN() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("modN");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" %ₙ ");
x_11 = lean::mk_nat_obj(70u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_modN___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("modN");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_modN(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_modN___closed__1;
x_4 = l_Lean_Parser_Term_modN;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_le() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("le");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" ≤ ");
x_11 = lean::mk_string(" <= ");
x_12 = lean::mk_nat_obj(50u);
x_13 = l_Lean_Parser_Term_unicodeInfixL(x_10, x_11, x_12);
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_le___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("le");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_le(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_le___closed__1;
x_4 = l_Lean_Parser_Term_le;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_ge() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("ge");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" ≥ ");
x_11 = lean::mk_string(" >= ");
x_12 = lean::mk_nat_obj(50u);
x_13 = l_Lean_Parser_Term_unicodeInfixL(x_10, x_11, x_12);
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_ge___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("ge");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_ge(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_ge___closed__1;
x_4 = l_Lean_Parser_Term_ge;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_lt() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("lt");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" < ");
x_11 = lean::mk_nat_obj(50u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_lt___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("lt");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_lt(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_lt___closed__1;
x_4 = l_Lean_Parser_Term_lt;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_gt() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("gt");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" > ");
x_11 = lean::mk_nat_obj(50u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_gt___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("gt");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_gt(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_gt___closed__1;
x_4 = l_Lean_Parser_Term_gt;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_eq() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("eq");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" = ");
x_11 = lean::mk_nat_obj(50u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_eq___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("eq");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_eq(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_eq___closed__1;
x_4 = l_Lean_Parser_Term_eq;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_beq() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("beq");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" == ");
x_11 = lean::mk_nat_obj(50u);
x_12 = l_Lean_Parser_Term_infixL(x_10, x_11);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_beq___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("beq");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_beq(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_beq___closed__1;
x_4 = l_Lean_Parser_Term_beq;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_and() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("and");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" ∧ ");
x_11 = lean::mk_string(" /\\ ");
x_12 = lean::mk_nat_obj(35u);
x_13 = l_Lean_Parser_Term_unicodeInfixR(x_10, x_11, x_12);
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_and___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("and");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_and(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_and___closed__1;
x_4 = l_Lean_Parser_Term_and;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_or() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("or");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" ∨ ");
x_11 = lean::mk_string(" \\/ ");
x_12 = lean::mk_nat_obj(30u);
x_13 = l_Lean_Parser_Term_unicodeInfixR(x_10, x_11, x_12);
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_or___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("or");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_or(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_or___closed__1;
x_4 = l_Lean_Parser_Term_or;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_iff() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("iff");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string(" ↔ ");
x_11 = lean::mk_string(" <-> ");
x_12 = lean::mk_nat_obj(20u);
x_13 = l_Lean_Parser_Term_unicodeInfixL(x_10, x_11, x_12);
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_17, 0, x_9);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _init_l___regBuiltinParser_Lean_Parser_Term_iff___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Term");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("iff");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_iff(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l___regBuiltinParser_Lean_Parser_Term_iff___closed__1;
x_4 = l_Lean_Parser_Term_iff;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* initialize_init_lean_parser_parser(obj*);
obj* initialize_init_lean_parser_level(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_term(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_level(w);
if (io_result_is_error(w)) return w;
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinTermParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinTermParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinTermParsingTable"), l_Lean_Parser_builtinTermParsingTable);
l_Lean_Parser_regBuiltinTermParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__1);
l_Lean_Parser_regBuiltinTermParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinTermParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_termParserFn___rarg___closed__1 = _init_l_Lean_Parser_termParserFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_termParserFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "termParserFn"), 1, l_Lean_Parser_termParserFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "termParser"), 2, l_Lean_Parser_termParser___boxed);
l_Lean_Parser_Term_unicodeInfixR___closed__1 = _init_l_Lean_Parser_Term_unicodeInfixR___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_unicodeInfixR___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "unicodeInfixR"), 3, l_Lean_Parser_Term_unicodeInfixR___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "infixR"), 2, l_Lean_Parser_Term_infixR___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "unicodeInfixL"), 3, l_Lean_Parser_Term_unicodeInfixL___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "infixL"), 2, l_Lean_Parser_Term_infixL___boxed);
l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1 = _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1();
lean::mark_persistent(l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__1);
l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2 = _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2();
lean::mark_persistent(l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___spec__3___closed__2);
l_Lean_Parser_Term_id = _init_l_Lean_Parser_Term_id();
lean::mark_persistent(l_Lean_Parser_Term_id);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "id"), l_Lean_Parser_Term_id);
l___regBuiltinParser_Lean_Parser_Term_id___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_id___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_id___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_id(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_num = _init_l_Lean_Parser_Term_num();
lean::mark_persistent(l_Lean_Parser_Term_num);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "num"), l_Lean_Parser_Term_num);
l___regBuiltinParser_Lean_Parser_Term_num___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_num___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_num___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_num(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_str = _init_l_Lean_Parser_Term_str();
lean::mark_persistent(l_Lean_Parser_Term_str);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "str"), l_Lean_Parser_Term_str);
l___regBuiltinParser_Lean_Parser_Term_str___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_str___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_str___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_str(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_type = _init_l_Lean_Parser_Term_type();
lean::mark_persistent(l_Lean_Parser_Term_type);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "type"), l_Lean_Parser_Term_type);
l___regBuiltinParser_Lean_Parser_Term_type___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_type___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_type___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_type(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sort = _init_l_Lean_Parser_Term_sort();
lean::mark_persistent(l_Lean_Parser_Term_sort);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sort"), l_Lean_Parser_Term_sort);
l___regBuiltinParser_Lean_Parser_Term_sort___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_sort___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_sort___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_sort(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_hole = _init_l_Lean_Parser_Term_hole();
lean::mark_persistent(l_Lean_Parser_Term_hole);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "hole"), l_Lean_Parser_Term_hole);
l___regBuiltinParser_Lean_Parser_Term_hole___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_hole___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_hole___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_hole(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sorry = _init_l_Lean_Parser_Term_sorry();
lean::mark_persistent(l_Lean_Parser_Term_sorry);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sorry"), l_Lean_Parser_Term_sorry);
l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_sorry(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_cdot = _init_l_Lean_Parser_Term_cdot();
lean::mark_persistent(l_Lean_Parser_Term_cdot);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "cdot"), l_Lean_Parser_Term_cdot);
l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_cdot(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_typeAscription = _init_l_Lean_Parser_Term_typeAscription();
lean::mark_persistent(l_Lean_Parser_Term_typeAscription);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "typeAscription"), l_Lean_Parser_Term_typeAscription);
l_Lean_Parser_Term_tupleTail = _init_l_Lean_Parser_Term_tupleTail();
lean::mark_persistent(l_Lean_Parser_Term_tupleTail);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "tupleTail"), l_Lean_Parser_Term_tupleTail);
l_Lean_Parser_Term_parenSpecial = _init_l_Lean_Parser_Term_parenSpecial();
lean::mark_persistent(l_Lean_Parser_Term_parenSpecial);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "parenSpecial"), l_Lean_Parser_Term_parenSpecial);
l_Lean_Parser_Term_paren = _init_l_Lean_Parser_Term_paren();
lean::mark_persistent(l_Lean_Parser_Term_paren);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "paren"), l_Lean_Parser_Term_paren);
l___regBuiltinParser_Lean_Parser_Term_paren___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_paren___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_paren___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_paren(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_anonymousCtor = _init_l_Lean_Parser_Term_anonymousCtor();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "anonymousCtor"), l_Lean_Parser_Term_anonymousCtor);
l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_optIdent = _init_l_Lean_Parser_Term_optIdent();
lean::mark_persistent(l_Lean_Parser_Term_optIdent);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "optIdent"), l_Lean_Parser_Term_optIdent);
l_Lean_Parser_Term_if = _init_l_Lean_Parser_Term_if();
lean::mark_persistent(l_Lean_Parser_Term_if);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "if"), l_Lean_Parser_Term_if);
l___regBuiltinParser_Lean_Parser_Term_if___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_if___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_if___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_if(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_fromTerm = _init_l_Lean_Parser_Term_fromTerm();
lean::mark_persistent(l_Lean_Parser_Term_fromTerm);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "fromTerm"), l_Lean_Parser_Term_fromTerm);
l_Lean_Parser_Term_haveAssign = _init_l_Lean_Parser_Term_haveAssign();
lean::mark_persistent(l_Lean_Parser_Term_haveAssign);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "haveAssign"), l_Lean_Parser_Term_haveAssign);
l_Lean_Parser_Term_have = _init_l_Lean_Parser_Term_have();
lean::mark_persistent(l_Lean_Parser_Term_have);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "have"), l_Lean_Parser_Term_have);
l___regBuiltinParser_Lean_Parser_Term_have___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_have___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_have___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_have(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_suffices = _init_l_Lean_Parser_Term_suffices();
lean::mark_persistent(l_Lean_Parser_Term_suffices);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "suffices"), l_Lean_Parser_Term_suffices);
l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_suffices(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_show = _init_l_Lean_Parser_Term_show();
lean::mark_persistent(l_Lean_Parser_Term_show);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "show"), l_Lean_Parser_Term_show);
l___regBuiltinParser_Lean_Parser_Term_show___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_show___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_show___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_show(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_fun = _init_l_Lean_Parser_Term_fun();
lean::mark_persistent(l_Lean_Parser_Term_fun);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "fun"), l_Lean_Parser_Term_fun);
l___regBuiltinParser_Lean_Parser_Term_fun___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_fun___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_fun___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_fun(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_structInstField = _init_l_Lean_Parser_Term_structInstField();
lean::mark_persistent(l_Lean_Parser_Term_structInstField);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "structInstField"), l_Lean_Parser_Term_structInstField);
l_Lean_Parser_Term_structInstSource = _init_l_Lean_Parser_Term_structInstSource();
lean::mark_persistent(l_Lean_Parser_Term_structInstSource);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "structInstSource"), l_Lean_Parser_Term_structInstSource);
l_Lean_Parser_Term_structInst = _init_l_Lean_Parser_Term_structInst();
lean::mark_persistent(l_Lean_Parser_Term_structInst);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "structInst"), l_Lean_Parser_Term_structInst);
l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_structInst(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_typeSpec = _init_l_Lean_Parser_Term_typeSpec();
lean::mark_persistent(l_Lean_Parser_Term_typeSpec);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "typeSpec"), l_Lean_Parser_Term_typeSpec);
l_Lean_Parser_Term_optType = _init_l_Lean_Parser_Term_optType();
lean::mark_persistent(l_Lean_Parser_Term_optType);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "optType"), l_Lean_Parser_Term_optType);
l_Lean_Parser_Term_subtype = _init_l_Lean_Parser_Term_subtype();
lean::mark_persistent(l_Lean_Parser_Term_subtype);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "subtype"), l_Lean_Parser_Term_subtype);
l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_subtype(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__1 = _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__1();
lean::mark_persistent(l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__1);
l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__2 = _init_l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__2();
lean::mark_persistent(l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___spec__3___closed__2);
l_Lean_Parser_Term_list = _init_l_Lean_Parser_Term_list();
lean::mark_persistent(l_Lean_Parser_Term_list);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "list"), l_Lean_Parser_Term_list);
l___regBuiltinParser_Lean_Parser_Term_list___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_list___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_list___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_list(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_binderIdent = _init_l_Lean_Parser_Term_binderIdent();
lean::mark_persistent(l_Lean_Parser_Term_binderIdent);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "binderIdent"), l_Lean_Parser_Term_binderIdent);
l_Lean_Parser_Term_binderType___closed__1 = _init_l_Lean_Parser_Term_binderType___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_binderType___closed__1);
l_Lean_Parser_Term_binderType___closed__2 = _init_l_Lean_Parser_Term_binderType___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_binderType___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "binderType"), 1, l_Lean_Parser_Term_binderType___boxed);
l_Lean_Parser_Term_binderDefault = _init_l_Lean_Parser_Term_binderDefault();
lean::mark_persistent(l_Lean_Parser_Term_binderDefault);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "binderDefault"), l_Lean_Parser_Term_binderDefault);
l_Lean_Parser_Term_binderTactic = _init_l_Lean_Parser_Term_binderTactic();
lean::mark_persistent(l_Lean_Parser_Term_binderTactic);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "binderTactic"), l_Lean_Parser_Term_binderTactic);
l_Lean_Parser_Term_explicitBinder___closed__1 = _init_l_Lean_Parser_Term_explicitBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__1);
l_Lean_Parser_Term_explicitBinder___closed__2 = _init_l_Lean_Parser_Term_explicitBinder___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "explicitBinder"), 1, l_Lean_Parser_Term_explicitBinder___boxed);
l_Lean_Parser_Term_implicitBinder___closed__1 = _init_l_Lean_Parser_Term_implicitBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__1);
l_Lean_Parser_Term_implicitBinder___closed__2 = _init_l_Lean_Parser_Term_implicitBinder___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "implicitBinder"), 1, l_Lean_Parser_Term_implicitBinder___boxed);
l_Lean_Parser_Term_instBinder = _init_l_Lean_Parser_Term_instBinder();
lean::mark_persistent(l_Lean_Parser_Term_instBinder);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "instBinder"), l_Lean_Parser_Term_instBinder);
l_Lean_Parser_Term_bracktedBinder___closed__1 = _init_l_Lean_Parser_Term_bracktedBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_bracktedBinder___closed__1);
l_Lean_Parser_Term_bracktedBinder___closed__2 = _init_l_Lean_Parser_Term_bracktedBinder___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_bracktedBinder___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "bracktedBinder"), 1, l_Lean_Parser_Term_bracktedBinder___boxed);
l_Lean_Parser_Term_depArrow = _init_l_Lean_Parser_Term_depArrow();
lean::mark_persistent(l_Lean_Parser_Term_depArrow);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "depArrow"), l_Lean_Parser_Term_depArrow);
l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_depArrow(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_simpleBinder = _init_l_Lean_Parser_Term_simpleBinder();
lean::mark_persistent(l_Lean_Parser_Term_simpleBinder);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "simpleBinder"), l_Lean_Parser_Term_simpleBinder);
l_Lean_Parser_Term_forall = _init_l_Lean_Parser_Term_forall();
lean::mark_persistent(l_Lean_Parser_Term_forall);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "forall"), l_Lean_Parser_Term_forall);
l___regBuiltinParser_Lean_Parser_Term_forall___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_forall___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_forall___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_forall(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_equation = _init_l_Lean_Parser_Term_equation();
lean::mark_persistent(l_Lean_Parser_Term_equation);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "equation"), l_Lean_Parser_Term_equation);
l_Lean_Parser_Term_match = _init_l_Lean_Parser_Term_match();
lean::mark_persistent(l_Lean_Parser_Term_match);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "match"), l_Lean_Parser_Term_match);
l___regBuiltinParser_Lean_Parser_Term_match___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_match___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_match___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_match(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_nomatch = _init_l_Lean_Parser_Term_nomatch();
lean::mark_persistent(l_Lean_Parser_Term_nomatch);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "nomatch"), l_Lean_Parser_Term_nomatch);
l___regBuiltinParser_Lean_Parser_Term_nomatch___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_nomatch___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_nomatch___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_nomatch(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_namedArgument = _init_l_Lean_Parser_Term_namedArgument();
lean::mark_persistent(l_Lean_Parser_Term_namedArgument);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "namedArgument"), l_Lean_Parser_Term_namedArgument);
l_Lean_Parser_Term_app = _init_l_Lean_Parser_Term_app();
lean::mark_persistent(l_Lean_Parser_Term_app);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "app"), l_Lean_Parser_Term_app);
l___regBuiltinParser_Lean_Parser_Term_app___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_app___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_app___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_app(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_proj = _init_l_Lean_Parser_Term_proj();
lean::mark_persistent(l_Lean_Parser_Term_proj);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "proj"), l_Lean_Parser_Term_proj);
l___regBuiltinParser_Lean_Parser_Term_proj___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_proj___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_proj___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_proj(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_arrow = _init_l_Lean_Parser_Term_arrow();
lean::mark_persistent(l_Lean_Parser_Term_arrow);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "arrow"), l_Lean_Parser_Term_arrow);
l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_arrow(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_array = _init_l_Lean_Parser_Term_array();
lean::mark_persistent(l_Lean_Parser_Term_array);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "array"), l_Lean_Parser_Term_array);
l___regBuiltinParser_Lean_Parser_Term_array___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_array___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_array___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_array(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_fcomp = _init_l_Lean_Parser_Term_fcomp();
lean::mark_persistent(l_Lean_Parser_Term_fcomp);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "fcomp"), l_Lean_Parser_Term_fcomp);
l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_fcomp(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_add = _init_l_Lean_Parser_Term_add();
lean::mark_persistent(l_Lean_Parser_Term_add);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "add"), l_Lean_Parser_Term_add);
l___regBuiltinParser_Lean_Parser_Term_add___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_add___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_add___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_add(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sub = _init_l_Lean_Parser_Term_sub();
lean::mark_persistent(l_Lean_Parser_Term_sub);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sub"), l_Lean_Parser_Term_sub);
l___regBuiltinParser_Lean_Parser_Term_sub___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_sub___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_sub___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_sub(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_mul = _init_l_Lean_Parser_Term_mul();
lean::mark_persistent(l_Lean_Parser_Term_mul);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "mul"), l_Lean_Parser_Term_mul);
l___regBuiltinParser_Lean_Parser_Term_mul___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_mul___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_mul___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_mul(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_div = _init_l_Lean_Parser_Term_div();
lean::mark_persistent(l_Lean_Parser_Term_div);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "div"), l_Lean_Parser_Term_div);
l___regBuiltinParser_Lean_Parser_Term_div___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_div___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_div___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_div(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_mod = _init_l_Lean_Parser_Term_mod();
lean::mark_persistent(l_Lean_Parser_Term_mod);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "mod"), l_Lean_Parser_Term_mod);
l___regBuiltinParser_Lean_Parser_Term_mod___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_mod___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_mod___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_mod(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_modN = _init_l_Lean_Parser_Term_modN();
lean::mark_persistent(l_Lean_Parser_Term_modN);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "modN"), l_Lean_Parser_Term_modN);
l___regBuiltinParser_Lean_Parser_Term_modN___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_modN___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_modN___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_modN(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_le = _init_l_Lean_Parser_Term_le();
lean::mark_persistent(l_Lean_Parser_Term_le);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "le"), l_Lean_Parser_Term_le);
l___regBuiltinParser_Lean_Parser_Term_le___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_le___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_le___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_le(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_ge = _init_l_Lean_Parser_Term_ge();
lean::mark_persistent(l_Lean_Parser_Term_ge);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "ge"), l_Lean_Parser_Term_ge);
l___regBuiltinParser_Lean_Parser_Term_ge___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_ge___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_ge___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_ge(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_lt = _init_l_Lean_Parser_Term_lt();
lean::mark_persistent(l_Lean_Parser_Term_lt);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "lt"), l_Lean_Parser_Term_lt);
l___regBuiltinParser_Lean_Parser_Term_lt___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_lt___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_lt___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_lt(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_gt = _init_l_Lean_Parser_Term_gt();
lean::mark_persistent(l_Lean_Parser_Term_gt);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "gt"), l_Lean_Parser_Term_gt);
l___regBuiltinParser_Lean_Parser_Term_gt___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_gt___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_gt___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_gt(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_eq = _init_l_Lean_Parser_Term_eq();
lean::mark_persistent(l_Lean_Parser_Term_eq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "eq"), l_Lean_Parser_Term_eq);
l___regBuiltinParser_Lean_Parser_Term_eq___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_eq___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_eq___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_eq(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_beq = _init_l_Lean_Parser_Term_beq();
lean::mark_persistent(l_Lean_Parser_Term_beq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "beq"), l_Lean_Parser_Term_beq);
l___regBuiltinParser_Lean_Parser_Term_beq___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_beq___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_beq___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_beq(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_and = _init_l_Lean_Parser_Term_and();
lean::mark_persistent(l_Lean_Parser_Term_and);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "and"), l_Lean_Parser_Term_and);
l___regBuiltinParser_Lean_Parser_Term_and___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_and___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_and___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_and(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_or = _init_l_Lean_Parser_Term_or();
lean::mark_persistent(l_Lean_Parser_Term_or);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "or"), l_Lean_Parser_Term_or);
l___regBuiltinParser_Lean_Parser_Term_or___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_or___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_or___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_or(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_iff = _init_l_Lean_Parser_Term_iff();
lean::mark_persistent(l_Lean_Parser_Term_iff);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "iff"), l_Lean_Parser_Term_iff);
l___regBuiltinParser_Lean_Parser_Term_iff___closed__1 = _init_l___regBuiltinParser_Lean_Parser_Term_iff___closed__1();
lean::mark_persistent(l___regBuiltinParser_Lean_Parser_Term_iff___closed__1);
w = l___regBuiltinParser_Lean_Parser_Term_iff(w);
if (io_result_is_error(w)) return w;
return w;
}
