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
uint8 l_Lean_Parser_checkTailNoWs(obj*);
obj* l_Lean_Parser_Term_arrow;
obj* l_Lean_Parser_Term_structInstSource;
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj*);
obj* l_Lean_Parser_Term_subtype___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_add___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser(uint8, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_ge___closed__1;
obj* l_Lean_Parser_Term_hole___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Term_show___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_hole___elambda__1(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Term_unicodeInfixL(obj*, obj*, obj*);
extern obj* l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
obj* l_Lean_Parser_Term_sorry___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_fromTerm;
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor___closed__1;
obj* l_Lean_Parser_Term_binderTactic___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_add(obj*);
obj* l_Lean_Parser_Term_haveAssign___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_suffices___closed__1;
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_forall(obj*);
obj* l_Lean_Parser_Term_infixR___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_le;
extern obj* l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2;
obj* l_Lean_Parser_Term_mod___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_Term_nomatch___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_lt___closed__1;
obj* l_Lean_Parser_Term_list___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepByFn___main(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_cdot___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Term_parenSpecial;
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_Term_and;
obj* l_Lean_Parser_Term_hole;
obj* l_Lean_Parser_termParserFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_have;
obj* l_Lean_Parser_Term_modN;
obj* l_Lean_Parser_Term_sort___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_namedArgument___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder___closed__3;
obj* l_Lean_Parser_Term_subtype___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_if(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_fun(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp(obj*);
obj* l_Lean_Parser_Term_type___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
obj* l_Lean_Parser_builtinTermParsingTable;
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj*);
obj* l_Lean_Parser_Term_binderType___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sorry___closed__1;
obj* l_Lean_Parser_sepBy1Fn___main(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_tupleTail;
obj* l___regBuiltinParser_Lean_Parser_Term_app___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_have___closed__1;
obj* l_Lean_Parser_Term_app___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_fun___closed__1;
obj* l_Lean_Parser_Term_tupleTail___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_namedArgument___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_infixR(obj*, obj*);
extern obj* l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1;
extern obj* l_Lean_Parser_appPrec;
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow___closed__1;
obj* l_Lean_Parser_Term_binderTactic;
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_sub___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_tupleTail___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_if___closed__1;
obj* l_Lean_Parser_Term_beq;
obj* l_Lean_Parser_Term_suffices;
extern obj* l_Lean_Parser_symbolFn___rarg___closed__1;
obj* l_Lean_Parser_Term_mul___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_explicitBinder___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder(uint8);
obj* l_Lean_Parser_Term_sub;
obj* l_Lean_Parser_Term_mul;
obj* l_Lean_Parser_Term_explicitBinder___closed__10;
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_list___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_Lean_Parser_termParserFn___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_or___closed__1;
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_Term_arrow___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_show___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_ge___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_proj___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder___closed__2;
obj* l_Lean_Parser_Term_structInst;
obj* l_Lean_Parser_Term_le___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_infixL(obj*, obj*);
obj* l_Lean_Parser_Term_str;
obj* l_Lean_Parser_Term_modN___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_fieldIdxFn(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_modN(obj*);
obj* l_Lean_Parser_Term_equation;
obj* l_Lean_Parser_Term_implicitBinder___closed__5;
obj* l___regBuiltinParser_Lean_Parser_Term_cdot___closed__1;
obj* l_Lean_Parser_Term_id;
obj* l_Lean_Parser_Term_structInst___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_add;
obj* l_Lean_Parser_Term_type___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_haveAssign;
obj* l___regBuiltinParser_Lean_Parser_Term_proj(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj*);
obj* l_Lean_Parser_Term_explicitBinder___closed__8;
obj* l_Lean_Parser_Term_depArrow;
obj* l___regBuiltinParser_Lean_Parser_Term_mul___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_le(obj*);
obj* l_Lean_Parser_Term_fcomp;
obj* l_Lean_Parser_Term_unicodeInfixR___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_paren___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_proj___closed__1;
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_suffices(obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
obj* l_Lean_Parser_Term_implicitBinder___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_levelParserFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_typeSpec___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderIdent;
obj* l_Lean_Parser_Term_structInstField___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_unicodeInfixR(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType(uint8);
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_structInst___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_eq(obj*);
obj* l_Lean_Parser_Term_paren___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Term_nomatch___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_array(obj*);
obj* l_Lean_Parser_Term_if;
obj* l___regBuiltinParser_Lean_Parser_Term_iff(obj*);
obj* l_Lean_Parser_termParserFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
obj* l_Lean_Parser_Term_explicitBinder___closed__11;
obj* l_Lean_Parser_Term_eq___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_iff;
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj*);
obj* l_Lean_Parser_Term_typeAscription___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_type___closed__1;
obj* l_Lean_Parser_Term_simpleBinder;
obj* l_Lean_Parser_termParser___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_suffices___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_iff___closed__1;
obj* l_Lean_Parser_Term_implicitBinder___closed__4;
obj* l_Lean_Parser_Term_bracktedBinder___closed__2;
obj* l_Lean_Parser_Term_explicitBinder___closed__6;
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_tryFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_cdot;
obj* l_Lean_Parser_Term_gt;
obj* l_Lean_Parser_Term_paren;
obj* l___regBuiltinParser_Lean_Parser_Term_modN___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sorry(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Term_sort;
obj* l_Lean_Parser_Term_infixL___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_gt___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_hole___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_match(obj*);
obj* l_Lean_Parser_Term_fun___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_Term_fromTerm___elambda__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_Term_sorry;
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_match;
obj* l_Lean_Parser_Term_explicitBinder___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Term_fcomp___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInst___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_structInst(obj*);
obj* l_Lean_Parser_Term_explicitBinder___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_unicodeInfixL___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_paren___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
obj* l_Lean_Parser_Term_have___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolCheckPrecFnAux(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_have___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_strAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_add___closed__1;
obj* l_Lean_Parser_Term_equation___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_subtype;
obj* l_Lean_Parser_Term_if___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_forall;
obj* l_Lean_Parser_Term_explicitBinder___closed__3;
obj* l___regBuiltinParser_Lean_Parser_Term_and(obj*);
obj* l_Lean_Parser_Term_mod;
obj* l___regBuiltinParser_Lean_Parser_Term_forall___closed__1;
obj* l_Lean_Parser_Term_proj;
obj* l_Lean_Parser_Term_forall___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_array___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj*);
obj* l_Lean_Parser_Term_equation___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_sub(obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l_Lean_Parser_Term_array___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_nomatch(obj*);
obj* l_Lean_Parser_Term_explicitBinder___closed__2;
obj* l_Lean_Parser_Term_fun___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_and___closed__1;
obj* l_Lean_Parser_Term_iff___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_match___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_id(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow(obj*);
obj* l_Lean_Parser_Term_instBinder___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_div(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mod___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj*);
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_unicodeInfixR___boxed(obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_id___closed__1;
obj* l_Lean_Parser_optionalFn___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_symbolNoWsFn___closed__1;
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_or;
obj* l_Lean_Parser_Term_simpleBinder___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderDefault;
obj* l_Lean_Parser_Term_explicitBinder___closed__4;
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_show;
obj* l_Lean_Parser_Term_explicitBinder(uint8);
obj* l_Lean_Parser_Term_instBinder___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_explicitBinder___closed__5;
obj* l_Lean_Parser_symbolNoWsInfo(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_or(obj*);
obj* l_Lean_Parser_Term_instBinder;
obj* l___regBuiltinParser_Lean_Parser_Term_arrow(obj*);
obj* l_Lean_Parser_Term_div___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_le___closed__1;
obj* l_Lean_Parser_Term_lt___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkError(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_have(obj*);
obj* l_Lean_Parser_Term_list;
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Lean_Parser_Term_implicitBinder___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_proj___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_Term_binderTactic___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_fromTerm___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_eq___closed__1;
obj* l_Lean_Parser_Term_typeAscription;
obj* l_Lean_Parser_termParserFn(uint8);
obj* l_Lean_Parser_Term_structInstSource___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder___closed__6;
obj* l___regBuiltinParser_Lean_Parser_Term_div___closed__1;
obj* l_Lean_Parser_identFn___boxed(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_subtype___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj*);
obj* l_Lean_Parser_Term_beq___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder___boxed(obj*);
obj* l_Lean_Parser_Term_bracktedBinder(uint8);
obj* l_Lean_Parser_Term_sort___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_optIdent;
obj* l___regBuiltinParser_Lean_Parser_Term_show(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_arrow___closed__1;
obj* l_Lean_Parser_Term_array___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParserFn___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_beq(obj*);
obj* l_Lean_Parser_Term_implicitBinder___closed__7;
obj* l_Lean_Parser_Term_match___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_list(obj*);
obj* l_Lean_Parser_Term_explicitBinder___boxed(obj*);
obj* l_Lean_Parser_Term_nomatch;
obj* l___regBuiltinParser_Lean_Parser_Term_ge(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj*);
obj* l_Lean_Parser_Term_typeAscription___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolInfo(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_type;
obj* l___regBuiltinParser_Lean_Parser_Term_subtype(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mod(obj*);
obj* l_Lean_Parser_Term_haveAssign___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInstField___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType___boxed(obj*);
obj* l_Lean_Parser_Term_anonymousCtor;
obj* l_Lean_Parser_Term_implicitBinder___closed__1;
obj* l_Lean_Parser_Term_binderDefault___elambda__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_Term_bracktedBinder___closed__1;
obj* l_Lean_Parser_Term_eq;
obj* l_Lean_Parser_Term_sorry___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_typeSpec___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_or___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_bracktedBinder___boxed(obj*);
obj* l_Lean_Parser_Term_structInstField;
obj* l_Lean_Parser_Term_binderDefault___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_gt___closed__1;
obj* l_Lean_Parser_Term_explicitBinder___closed__7;
obj* l_Lean_Parser_Term_forall___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_beq___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_gt(obj*);
obj* l_Lean_Parser_Term_div;
obj* l_Lean_Parser_Term_explicitBinder___closed__9;
obj* l_Lean_Parser_Term_suffices___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_if___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_typeSpec;
obj* l_Lean_Parser_Term_structInstSource___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_ge;
obj* l___regBuiltinParser_Lean_Parser_Term_list___closed__1;
obj* l_Lean_Parser_Term_fun;
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_and___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mul(obj*);
obj* l_Lean_Parser_Term_cdot___elambda__1(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Term_id___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
lean::inc(x_7);
x_11 = l_Lean_Parser_identFn___rarg(x_7, x_8);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = lean::array_get_size(x_13);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
x_16 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_17 = lean::string_append(x_16, x_2);
x_18 = l_Char_HasRepr___closed__1;
x_19 = lean::string_append(x_17, x_18);
lean::inc(x_7);
x_20 = l_Lean_Parser_symbolFnAux(x_2, x_19, x_7, x_11);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; uint8 x_23; obj* x_24; obj* x_25; 
x_22 = 0;
x_23 = 0;
lean::inc(x_7);
x_24 = l_Lean_Parser_sepBy1Fn___main(x_22, x_23, x_3, x_4, x_6, x_7, x_20);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::string_append(x_16, x_5);
x_27 = lean::string_append(x_26, x_18);
x_28 = l_Lean_Parser_symbolFnAux(x_5, x_27, x_7, x_24);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_15);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_28, x_30, x_14);
x_32 = l_Lean_Parser_ParserState_mkNode(x_31, x_1, x_10);
return x_32;
}
else
{
obj* x_33; uint8 x_34; 
lean::dec(x_29);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
x_34 = lean::nat_dec_eq(x_33, x_15);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_15);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_28, x_35, x_14);
x_37 = l_Lean_Parser_ParserState_mkNode(x_36, x_1, x_10);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = l_Lean_Parser_ParserState_restore(x_28, x_14, x_15);
x_39 = l_Lean_nullKind;
x_40 = l_Lean_Parser_ParserState_mkNode(x_38, x_39, x_14);
x_41 = l_Lean_Parser_ParserState_mkNode(x_40, x_1, x_10);
return x_41;
}
}
}
else
{
obj* x_42; uint8 x_43; 
lean::dec(x_25);
lean::dec(x_7);
x_42 = lean::cnstr_get(x_24, 1);
lean::inc(x_42);
x_43 = lean::nat_dec_eq(x_42, x_15);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_15);
x_44 = l_Lean_nullKind;
x_45 = l_Lean_Parser_ParserState_mkNode(x_24, x_44, x_14);
x_46 = l_Lean_Parser_ParserState_mkNode(x_45, x_1, x_10);
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_47 = l_Lean_Parser_ParserState_restore(x_24, x_14, x_15);
x_48 = l_Lean_nullKind;
x_49 = l_Lean_Parser_ParserState_mkNode(x_47, x_48, x_14);
x_50 = l_Lean_Parser_ParserState_mkNode(x_49, x_1, x_10);
return x_50;
}
}
}
else
{
obj* x_51; uint8 x_52; 
lean::dec(x_21);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
x_51 = lean::cnstr_get(x_20, 1);
lean::inc(x_51);
x_52 = lean::nat_dec_eq(x_51, x_15);
lean::dec(x_51);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_15);
x_53 = l_Lean_nullKind;
x_54 = l_Lean_Parser_ParserState_mkNode(x_20, x_53, x_14);
x_55 = l_Lean_Parser_ParserState_mkNode(x_54, x_1, x_10);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_56 = l_Lean_Parser_ParserState_restore(x_20, x_14, x_15);
x_57 = l_Lean_nullKind;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_14);
x_59 = l_Lean_Parser_ParserState_mkNode(x_58, x_1, x_10);
return x_59;
}
}
}
else
{
obj* x_60; 
lean::dec(x_12);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
x_60 = l_Lean_Parser_ParserState_mkNode(x_11, x_1, x_10);
return x_60;
}
}
}
obj* _init_l_Lean_Parser_Term_id() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
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
x_12 = lean::box(0);
x_13 = lean::mk_string(".{");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_15 = l_Lean_Parser_symbolInfo(x_14, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::mk_string(", ");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_12);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = l_Lean_Parser_sepBy1Info(x_18, x_23);
x_26 = lean::mk_string("}");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
x_28 = l_Lean_Parser_symbolInfo(x_27, x_12);
x_29 = l_Lean_Parser_andthenInfo(x_25, x_28);
x_30 = l_Lean_Parser_andthenInfo(x_15, x_29);
x_31 = l_Lean_Parser_noFirstTokenInfo(x_30);
x_32 = l_Lean_Parser_andthenInfo(x_11, x_31);
x_33 = l_Lean_Parser_nodeInfo(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_id___elambda__1___boxed), 8, 5);
lean::closure_set(x_34, 0, x_9);
lean::closure_set(x_34, 1, x_14);
lean::closure_set(x_34, 2, x_20);
lean::closure_set(x_34, 3, x_24);
lean::closure_set(x_34, 4, x_27);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
obj* l_Lean_Parser_Term_id___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_id___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_type___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_type() {
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
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_type___elambda__1___boxed), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Term_type___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_type___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_sort___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_sort() {
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
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sort___elambda__1___boxed), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Term_sort___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_sort___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_hole___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_hole() {
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
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_hole___elambda__1___boxed), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Term_hole___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_hole___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_sorry___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_sorry() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_14 = l_Lean_Parser_nodeInfo(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sorry___elambda__1___boxed), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_Lean_Parser_Term_sorry___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_sorry___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_cdot___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_cdot() {
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
x_15 = l_Lean_Parser_nodeInfo(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_cdot___elambda__1___boxed), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Term_cdot___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_cdot___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_typeAscription___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_typeAscription() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeAscription___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_typeAscription___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_typeAscription___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_tupleTail___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_11 = lean::string_append(x_10, x_2);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_11, x_12);
lean::inc(x_6);
x_14 = l_Lean_Parser_symbolFnAux(x_2, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_16 = 0;
x_17 = 0;
x_18 = l_Lean_Parser_sepBy1Fn___main(x_16, x_17, x_4, x_3, x_5, x_6, x_14);
x_19 = l_Lean_Parser_ParserState_mkNode(x_18, x_1, x_9);
return x_19;
}
else
{
obj* x_20; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_Lean_Parser_ParserState_mkNode(x_14, x_1, x_9);
return x_20;
}
}
}
obj* _init_l_Lean_Parser_Term_tupleTail() {
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
x_8 = lean::mk_string("tupleTail");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string(", ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
lean::inc(x_12);
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
lean::inc(x_13);
x_20 = l_Lean_Parser_sepBy1Info(x_17, x_13);
x_21 = l_Lean_Parser_andthenInfo(x_13, x_20);
x_22 = l_Lean_Parser_nodeInfo(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_tupleTail___elambda__1___boxed), 7, 4);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_12);
lean::closure_set(x_23, 2, x_14);
lean::closure_set(x_23, 3, x_19);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* l_Lean_Parser_Term_tupleTail___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Term_tupleTail___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
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
obj* l_Lean_Parser_Term_paren___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_11 = lean::string_append(x_10, x_2);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_11, x_12);
lean::inc(x_6);
x_14 = l_Lean_Parser_symbolFnAux(x_2, x_13, x_6, x_7);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_49 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_50 = l_Lean_Parser_builtinTermParsingTable;
x_51 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_52 = l_Lean_Parser_runBuiltinParserUnsafe(x_49, x_50, x_51, x_6, x_14);
x_53 = lean::cnstr_get(x_52, 3);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; 
lean::inc(x_6);
x_54 = lean::apply_3(x_3, x_5, x_6, x_52);
x_19 = x_54;
goto block_48;
}
else
{
lean::dec(x_53);
lean::dec(x_5);
lean::dec(x_3);
x_19 = x_52;
goto block_48;
}
block_48:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_18);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_19, x_21, x_17);
x_23 = lean::cnstr_get(x_22, 3);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::string_append(x_10, x_4);
x_25 = lean::string_append(x_24, x_12);
x_26 = l_Lean_Parser_symbolFnAux(x_4, x_25, x_6, x_22);
x_27 = l_Lean_Parser_ParserState_mkNode(x_26, x_1, x_9);
return x_27;
}
else
{
obj* x_28; 
lean::dec(x_23);
lean::dec(x_6);
x_28 = l_Lean_Parser_ParserState_mkNode(x_22, x_1, x_9);
return x_28;
}
}
else
{
obj* x_29; uint8 x_30; 
lean::dec(x_20);
x_29 = lean::cnstr_get(x_19, 1);
lean::inc(x_29);
x_30 = lean::nat_dec_eq(x_29, x_18);
lean::dec(x_29);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_18);
x_31 = l_Lean_nullKind;
x_32 = l_Lean_Parser_ParserState_mkNode(x_19, x_31, x_17);
x_33 = lean::cnstr_get(x_32, 3);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = lean::string_append(x_10, x_4);
x_35 = lean::string_append(x_34, x_12);
x_36 = l_Lean_Parser_symbolFnAux(x_4, x_35, x_6, x_32);
x_37 = l_Lean_Parser_ParserState_mkNode(x_36, x_1, x_9);
return x_37;
}
else
{
obj* x_38; 
lean::dec(x_33);
lean::dec(x_6);
x_38 = l_Lean_Parser_ParserState_mkNode(x_32, x_1, x_9);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
x_40 = l_Lean_nullKind;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_17);
x_42 = lean::cnstr_get(x_41, 3);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::string_append(x_10, x_4);
x_44 = lean::string_append(x_43, x_12);
x_45 = l_Lean_Parser_symbolFnAux(x_4, x_44, x_6, x_41);
x_46 = l_Lean_Parser_ParserState_mkNode(x_45, x_1, x_9);
return x_46;
}
else
{
obj* x_47; 
lean::dec(x_42);
lean::dec(x_6);
x_47 = l_Lean_Parser_ParserState_mkNode(x_41, x_1, x_9);
return x_47;
}
}
}
}
}
else
{
obj* x_55; 
lean::dec(x_15);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_55 = l_Lean_Parser_ParserState_mkNode(x_14, x_1, x_9);
return x_55;
}
}
}
obj* _init_l_Lean_Parser_Term_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_Term_parenSpecial;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = l_Lean_Parser_andthenInfo(x_17, x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
x_22 = l_Lean_Parser_noFirstTokenInfo(x_20);
x_23 = lean::box(0);
x_24 = lean::mk_string(")");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_23);
x_27 = l_Lean_Parser_andthenInfo(x_22, x_26);
x_28 = l_Lean_Parser_andthenInfo(x_14, x_27);
x_29 = l_Lean_Parser_nodeInfo(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_paren___elambda__1___boxed), 7, 4);
lean::closure_set(x_30, 0, x_9);
lean::closure_set(x_30, 1, x_13);
lean::closure_set(x_30, 2, x_21);
lean::closure_set(x_30, 3, x_25);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
obj* l_Lean_Parser_Term_paren___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Term_paren___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_2);
return x_8;
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
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_12 = lean::string_append(x_11, x_2);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_12, x_13);
lean::inc(x_7);
x_15 = l_Lean_Parser_symbolFnAux(x_2, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; uint8 x_18; obj* x_19; obj* x_20; 
x_17 = 0;
x_18 = 0;
lean::inc(x_7);
x_19 = l_Lean_Parser_sepBy1Fn___main(x_17, x_18, x_3, x_4, x_6, x_7, x_15);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::string_append(x_11, x_5);
x_22 = lean::string_append(x_21, x_13);
x_23 = l_Lean_Parser_symbolFnAux(x_5, x_22, x_7, x_19);
x_24 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_10);
return x_24;
}
else
{
obj* x_25; 
lean::dec(x_20);
lean::dec(x_7);
x_25 = l_Lean_Parser_ParserState_mkNode(x_19, x_1, x_10);
return x_25;
}
}
else
{
obj* x_26; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
x_26 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_10);
return x_26;
}
}
}
obj* _init_l_Lean_Parser_Term_anonymousCtor() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::box(0);
x_21 = lean::mk_string(", ");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = l_Lean_Parser_sepBy1Info(x_17, x_23);
x_26 = lean::mk_string("⟩");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
x_28 = l_Lean_Parser_symbolInfo(x_27, x_20);
x_29 = l_Lean_Parser_andthenInfo(x_25, x_28);
x_30 = l_Lean_Parser_andthenInfo(x_14, x_29);
x_31 = l_Lean_Parser_nodeInfo(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_anonymousCtor___elambda__1___boxed), 8, 5);
lean::closure_set(x_32, 0, x_9);
lean::closure_set(x_32, 1, x_13);
lean::closure_set(x_32, 2, x_19);
lean::closure_set(x_32, 3, x_24);
lean::closure_set(x_32, 4, x_27);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_anonymousCtor___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_if___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_38 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_39 = lean::string_append(x_38, x_2);
x_40 = l_Char_HasRepr___closed__1;
x_41 = lean::string_append(x_39, x_40);
lean::inc(x_7);
x_42 = l_Lean_Parser_symbolFnAux(x_2, x_41, x_7, x_8);
x_43 = lean::cnstr_get(x_42, 3);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
x_46 = lean::array_get_size(x_44);
lean::dec(x_44);
lean::inc(x_7);
x_47 = l_Lean_Parser_identFn___rarg(x_7, x_42);
x_48 = lean::cnstr_get(x_47, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_49 = lean::string_append(x_38, x_5);
x_50 = lean::string_append(x_49, x_40);
lean::inc(x_7);
x_51 = l_Lean_Parser_symbolFnAux(x_5, x_50, x_7, x_47);
x_52 = lean::cnstr_get(x_51, 3);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_45);
x_53 = l_Lean_nullKind;
x_54 = l_Lean_Parser_ParserState_mkNode(x_51, x_53, x_46);
x_11 = x_54;
goto block_37;
}
else
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_51);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_51, 0);
x_57 = lean::cnstr_get(x_51, 3);
lean::dec(x_57);
x_58 = lean::cnstr_get(x_51, 1);
lean::dec(x_58);
x_59 = l_Array_shrink___main___rarg(x_56, x_46);
lean::inc(x_45);
lean::cnstr_set(x_51, 1, x_45);
lean::cnstr_set(x_51, 0, x_59);
x_60 = lean::nat_dec_eq(x_45, x_45);
if (x_60 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_45);
x_61 = l_Lean_nullKind;
x_62 = l_Lean_Parser_ParserState_mkNode(x_51, x_61, x_46);
x_11 = x_62;
goto block_37;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_Lean_Parser_ParserState_restore(x_51, x_46, x_45);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_46);
x_11 = x_65;
goto block_37;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; uint8 x_70; 
x_66 = lean::cnstr_get(x_51, 0);
x_67 = lean::cnstr_get(x_51, 2);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_51);
x_68 = l_Array_shrink___main___rarg(x_66, x_46);
lean::inc(x_45);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_45);
lean::cnstr_set(x_69, 2, x_67);
lean::cnstr_set(x_69, 3, x_52);
x_70 = lean::nat_dec_eq(x_45, x_45);
if (x_70 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_45);
x_71 = l_Lean_nullKind;
x_72 = l_Lean_Parser_ParserState_mkNode(x_69, x_71, x_46);
x_11 = x_72;
goto block_37;
}
else
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_Lean_Parser_ParserState_restore(x_69, x_46, x_45);
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_73, x_74, x_46);
x_11 = x_75;
goto block_37;
}
}
}
}
else
{
obj* x_76; 
lean::dec(x_48);
x_76 = lean::cnstr_get(x_47, 3);
lean::inc(x_76);
if (lean::obj_tag(x_76) == 0)
{
obj* x_77; obj* x_78; 
lean::dec(x_45);
x_77 = l_Lean_nullKind;
x_78 = l_Lean_Parser_ParserState_mkNode(x_47, x_77, x_46);
x_11 = x_78;
goto block_37;
}
else
{
uint8 x_79; 
x_79 = !lean::is_exclusive(x_47);
if (x_79 == 0)
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; 
x_80 = lean::cnstr_get(x_47, 0);
x_81 = lean::cnstr_get(x_47, 3);
lean::dec(x_81);
x_82 = lean::cnstr_get(x_47, 1);
lean::dec(x_82);
x_83 = l_Array_shrink___main___rarg(x_80, x_46);
lean::inc(x_45);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 0, x_83);
x_84 = lean::nat_dec_eq(x_45, x_45);
if (x_84 == 0)
{
obj* x_85; obj* x_86; 
lean::dec(x_45);
x_85 = l_Lean_nullKind;
x_86 = l_Lean_Parser_ParserState_mkNode(x_47, x_85, x_46);
x_11 = x_86;
goto block_37;
}
else
{
obj* x_87; obj* x_88; obj* x_89; 
x_87 = l_Lean_Parser_ParserState_restore(x_47, x_46, x_45);
x_88 = l_Lean_nullKind;
x_89 = l_Lean_Parser_ParserState_mkNode(x_87, x_88, x_46);
x_11 = x_89;
goto block_37;
}
}
else
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; uint8 x_94; 
x_90 = lean::cnstr_get(x_47, 0);
x_91 = lean::cnstr_get(x_47, 2);
lean::inc(x_91);
lean::inc(x_90);
lean::dec(x_47);
x_92 = l_Array_shrink___main___rarg(x_90, x_46);
lean::inc(x_45);
x_93 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_45);
lean::cnstr_set(x_93, 2, x_91);
lean::cnstr_set(x_93, 3, x_76);
x_94 = lean::nat_dec_eq(x_45, x_45);
if (x_94 == 0)
{
obj* x_95; obj* x_96; 
lean::dec(x_45);
x_95 = l_Lean_nullKind;
x_96 = l_Lean_Parser_ParserState_mkNode(x_93, x_95, x_46);
x_11 = x_96;
goto block_37;
}
else
{
obj* x_97; obj* x_98; obj* x_99; 
x_97 = l_Lean_Parser_ParserState_restore(x_93, x_46, x_45);
x_98 = l_Lean_nullKind;
x_99 = l_Lean_Parser_ParserState_mkNode(x_97, x_98, x_46);
x_11 = x_99;
goto block_37;
}
}
}
}
}
else
{
obj* x_100; 
lean::dec(x_43);
lean::dec(x_7);
x_100 = l_Lean_Parser_ParserState_mkNode(x_42, x_1, x_10);
return x_100;
}
block_37:
{
obj* x_12; 
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_14 = l_Lean_Parser_builtinTermParsingTable;
x_15 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_16 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_15, x_7, x_11);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_19 = lean::string_append(x_18, x_3);
x_20 = l_Char_HasRepr___closed__1;
x_21 = lean::string_append(x_19, x_20);
lean::inc(x_7);
x_22 = l_Lean_Parser_symbolFnAux(x_3, x_21, x_7, x_16);
x_23 = lean::cnstr_get(x_22, 3);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; 
lean::inc(x_7);
x_24 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_15, x_7, x_22);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::string_append(x_18, x_4);
x_27 = lean::string_append(x_26, x_20);
lean::inc(x_7);
x_28 = l_Lean_Parser_symbolFnAux(x_4, x_27, x_7, x_24);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; 
x_30 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_15, x_7, x_28);
x_31 = l_Lean_Parser_ParserState_mkNode(x_30, x_1, x_10);
return x_31;
}
else
{
obj* x_32; 
lean::dec(x_29);
lean::dec(x_7);
x_32 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_10);
return x_32;
}
}
else
{
obj* x_33; 
lean::dec(x_25);
lean::dec(x_7);
x_33 = l_Lean_Parser_ParserState_mkNode(x_24, x_1, x_10);
return x_33;
}
}
else
{
obj* x_34; 
lean::dec(x_23);
lean::dec(x_7);
x_34 = l_Lean_Parser_ParserState_mkNode(x_22, x_1, x_10);
return x_34;
}
}
else
{
obj* x_35; 
lean::dec(x_17);
lean::dec(x_7);
x_35 = l_Lean_Parser_ParserState_mkNode(x_16, x_1, x_10);
return x_35;
}
}
else
{
obj* x_36; 
lean::dec(x_12);
lean::dec(x_7);
x_36 = l_Lean_Parser_ParserState_mkNode(x_11, x_1, x_10);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_Term_if() {
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
x_8 = lean::mk_string("if");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("if ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_string(" then ");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_19 = l_Lean_Parser_symbolInfo(x_18, x_10);
x_20 = lean::mk_string(" else ");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = l_Lean_Parser_symbolInfo(x_21, x_10);
lean::inc(x_16);
x_23 = l_Lean_Parser_andthenInfo(x_22, x_16);
lean::inc(x_16);
x_24 = l_Lean_Parser_andthenInfo(x_16, x_23);
x_25 = l_Lean_Parser_andthenInfo(x_19, x_24);
x_26 = l_Lean_Parser_andthenInfo(x_16, x_25);
x_27 = lean::mk_string("ident");
x_28 = l_Lean_Parser_mkAtomicInfo(x_27);
x_29 = lean::mk_string(" : ");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = l_Lean_Parser_symbolInfo(x_30, x_10);
x_32 = l_Lean_Parser_andthenInfo(x_28, x_31);
x_33 = l_Lean_Parser_noFirstTokenInfo(x_32);
x_34 = l_Lean_Parser_andthenInfo(x_33, x_26);
x_35 = l_Lean_Parser_andthenInfo(x_13, x_34);
x_36 = l_Lean_Parser_nodeInfo(x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_if___elambda__1___boxed), 8, 5);
lean::closure_set(x_37, 0, x_9);
lean::closure_set(x_37, 1, x_12);
lean::closure_set(x_37, 2, x_18);
lean::closure_set(x_37, 3, x_21);
lean::closure_set(x_37, 4, x_30);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
obj* l_Lean_Parser_Term_if___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_if___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_fromTerm___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_fromTerm() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fromTerm___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_fromTerm___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_fromTerm___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_haveAssign___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_haveAssign() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_haveAssign___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_haveAssign___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_haveAssign___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_have___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_52 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_53 = lean::string_append(x_52, x_2);
x_54 = l_Char_HasRepr___closed__1;
x_55 = lean::string_append(x_53, x_54);
lean::inc(x_8);
x_56 = l_Lean_Parser_symbolFnAux(x_2, x_55, x_8, x_9);
x_57 = lean::cnstr_get(x_56, 3);
lean::inc(x_57);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
x_60 = lean::array_get_size(x_58);
lean::dec(x_58);
lean::inc(x_8);
x_61 = l_Lean_Parser_identFn___rarg(x_8, x_56);
x_62 = lean::cnstr_get(x_61, 3);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_63 = lean::string_append(x_52, x_6);
x_64 = lean::string_append(x_63, x_54);
lean::inc(x_8);
x_65 = l_Lean_Parser_symbolFnAux(x_6, x_64, x_8, x_61);
x_66 = lean::cnstr_get(x_65, 3);
lean::inc(x_66);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_68; 
lean::dec(x_59);
x_67 = l_Lean_nullKind;
x_68 = l_Lean_Parser_ParserState_mkNode(x_65, x_67, x_60);
x_12 = x_68;
goto block_51;
}
else
{
uint8 x_69; 
x_69 = !lean::is_exclusive(x_65);
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; 
x_70 = lean::cnstr_get(x_65, 0);
x_71 = lean::cnstr_get(x_65, 3);
lean::dec(x_71);
x_72 = lean::cnstr_get(x_65, 1);
lean::dec(x_72);
x_73 = l_Array_shrink___main___rarg(x_70, x_60);
lean::inc(x_59);
lean::cnstr_set(x_65, 1, x_59);
lean::cnstr_set(x_65, 0, x_73);
x_74 = lean::nat_dec_eq(x_59, x_59);
if (x_74 == 0)
{
obj* x_75; obj* x_76; 
lean::dec(x_59);
x_75 = l_Lean_nullKind;
x_76 = l_Lean_Parser_ParserState_mkNode(x_65, x_75, x_60);
x_12 = x_76;
goto block_51;
}
else
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = l_Lean_Parser_ParserState_restore(x_65, x_60, x_59);
x_78 = l_Lean_nullKind;
x_79 = l_Lean_Parser_ParserState_mkNode(x_77, x_78, x_60);
x_12 = x_79;
goto block_51;
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; 
x_80 = lean::cnstr_get(x_65, 0);
x_81 = lean::cnstr_get(x_65, 2);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_65);
x_82 = l_Array_shrink___main___rarg(x_80, x_60);
lean::inc(x_59);
x_83 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_59);
lean::cnstr_set(x_83, 2, x_81);
lean::cnstr_set(x_83, 3, x_66);
x_84 = lean::nat_dec_eq(x_59, x_59);
if (x_84 == 0)
{
obj* x_85; obj* x_86; 
lean::dec(x_59);
x_85 = l_Lean_nullKind;
x_86 = l_Lean_Parser_ParserState_mkNode(x_83, x_85, x_60);
x_12 = x_86;
goto block_51;
}
else
{
obj* x_87; obj* x_88; obj* x_89; 
x_87 = l_Lean_Parser_ParserState_restore(x_83, x_60, x_59);
x_88 = l_Lean_nullKind;
x_89 = l_Lean_Parser_ParserState_mkNode(x_87, x_88, x_60);
x_12 = x_89;
goto block_51;
}
}
}
}
else
{
obj* x_90; 
lean::dec(x_62);
x_90 = lean::cnstr_get(x_61, 3);
lean::inc(x_90);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_92; 
lean::dec(x_59);
x_91 = l_Lean_nullKind;
x_92 = l_Lean_Parser_ParserState_mkNode(x_61, x_91, x_60);
x_12 = x_92;
goto block_51;
}
else
{
uint8 x_93; 
x_93 = !lean::is_exclusive(x_61);
if (x_93 == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; 
x_94 = lean::cnstr_get(x_61, 0);
x_95 = lean::cnstr_get(x_61, 3);
lean::dec(x_95);
x_96 = lean::cnstr_get(x_61, 1);
lean::dec(x_96);
x_97 = l_Array_shrink___main___rarg(x_94, x_60);
lean::inc(x_59);
lean::cnstr_set(x_61, 1, x_59);
lean::cnstr_set(x_61, 0, x_97);
x_98 = lean::nat_dec_eq(x_59, x_59);
if (x_98 == 0)
{
obj* x_99; obj* x_100; 
lean::dec(x_59);
x_99 = l_Lean_nullKind;
x_100 = l_Lean_Parser_ParserState_mkNode(x_61, x_99, x_60);
x_12 = x_100;
goto block_51;
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = l_Lean_Parser_ParserState_restore(x_61, x_60, x_59);
x_102 = l_Lean_nullKind;
x_103 = l_Lean_Parser_ParserState_mkNode(x_101, x_102, x_60);
x_12 = x_103;
goto block_51;
}
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; 
x_104 = lean::cnstr_get(x_61, 0);
x_105 = lean::cnstr_get(x_61, 2);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_61);
x_106 = l_Array_shrink___main___rarg(x_104, x_60);
lean::inc(x_59);
x_107 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_59);
lean::cnstr_set(x_107, 2, x_105);
lean::cnstr_set(x_107, 3, x_90);
x_108 = lean::nat_dec_eq(x_59, x_59);
if (x_108 == 0)
{
obj* x_109; obj* x_110; 
lean::dec(x_59);
x_109 = l_Lean_nullKind;
x_110 = l_Lean_Parser_ParserState_mkNode(x_107, x_109, x_60);
x_12 = x_110;
goto block_51;
}
else
{
obj* x_111; obj* x_112; obj* x_113; 
x_111 = l_Lean_Parser_ParserState_restore(x_107, x_60, x_59);
x_112 = l_Lean_nullKind;
x_113 = l_Lean_Parser_ParserState_mkNode(x_111, x_112, x_60);
x_12 = x_113;
goto block_51;
}
}
}
}
}
else
{
obj* x_114; 
lean::dec(x_57);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
x_114 = l_Lean_Parser_ParserState_mkNode(x_56, x_1, x_11);
return x_114;
}
block_51:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
lean::inc(x_8);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_8, x_12);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_20 = lean::array_get_size(x_19);
lean::dec(x_19);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
lean::inc(x_8);
lean::inc(x_7);
x_22 = lean::apply_3(x_3, x_7, x_8, x_17);
x_23 = lean::cnstr_get(x_22, 3);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_21);
lean::dec(x_20);
lean::dec(x_7);
lean::dec(x_4);
x_24 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_25 = lean::string_append(x_24, x_5);
x_26 = l_Char_HasRepr___closed__1;
x_27 = lean::string_append(x_25, x_26);
lean::inc(x_8);
x_28 = l_Lean_Parser_symbolFnAux(x_5, x_27, x_8, x_22);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; 
x_30 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_8, x_28);
x_31 = l_Lean_Parser_ParserState_mkNode(x_30, x_1, x_11);
return x_31;
}
else
{
obj* x_32; 
lean::dec(x_29);
lean::dec(x_8);
x_32 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_11);
return x_32;
}
}
else
{
obj* x_33; uint8 x_34; 
lean::dec(x_23);
x_33 = lean::cnstr_get(x_22, 1);
lean::inc(x_33);
x_34 = lean::nat_dec_eq(x_33, x_21);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_35; 
lean::dec(x_21);
lean::dec(x_20);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
x_35 = l_Lean_Parser_ParserState_mkNode(x_22, x_1, x_11);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_Lean_Parser_ParserState_restore(x_22, x_20, x_21);
lean::dec(x_20);
lean::inc(x_8);
x_37 = lean::apply_3(x_4, x_7, x_8, x_36);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_40 = lean::string_append(x_39, x_5);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean::string_append(x_40, x_41);
lean::inc(x_8);
x_43 = l_Lean_Parser_symbolFnAux(x_5, x_42, x_8, x_37);
x_44 = lean::cnstr_get(x_43, 3);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; 
x_45 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_8, x_43);
x_46 = l_Lean_Parser_ParserState_mkNode(x_45, x_1, x_11);
return x_46;
}
else
{
obj* x_47; 
lean::dec(x_44);
lean::dec(x_8);
x_47 = l_Lean_Parser_ParserState_mkNode(x_43, x_1, x_11);
return x_47;
}
}
else
{
obj* x_48; 
lean::dec(x_38);
lean::dec(x_8);
x_48 = l_Lean_Parser_ParserState_mkNode(x_37, x_1, x_11);
return x_48;
}
}
}
}
else
{
obj* x_49; 
lean::dec(x_18);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
x_49 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_11);
return x_49;
}
}
else
{
obj* x_50; 
lean::dec(x_13);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
x_50 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_11);
return x_50;
}
}
}
}
obj* _init_l_Lean_Parser_Term_have() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_Term_haveAssign;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = l_Lean_Parser_Term_fromTerm;
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_21 = l_Lean_Parser_orelseInfo(x_18, x_20);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_19, 1);
lean::inc(x_23);
x_24 = lean::mk_string("; ");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_10);
lean::inc(x_16);
x_27 = l_Lean_Parser_andthenInfo(x_26, x_16);
x_28 = l_Lean_Parser_andthenInfo(x_21, x_27);
x_29 = l_Lean_Parser_andthenInfo(x_16, x_28);
x_30 = lean::mk_string("ident");
x_31 = l_Lean_Parser_mkAtomicInfo(x_30);
x_32 = lean::mk_string(" : ");
x_33 = l_String_trim(x_32);
lean::dec(x_32);
lean::inc(x_33);
x_34 = l_Lean_Parser_symbolInfo(x_33, x_10);
x_35 = l_Lean_Parser_andthenInfo(x_31, x_34);
x_36 = l_Lean_Parser_noFirstTokenInfo(x_35);
x_37 = l_Lean_Parser_andthenInfo(x_36, x_29);
x_38 = l_Lean_Parser_andthenInfo(x_13, x_37);
x_39 = l_Lean_Parser_nodeInfo(x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_have___elambda__1___boxed), 9, 6);
lean::closure_set(x_40, 0, x_9);
lean::closure_set(x_40, 1, x_12);
lean::closure_set(x_40, 2, x_22);
lean::closure_set(x_40, 3, x_23);
lean::closure_set(x_40, 4, x_25);
lean::closure_set(x_40, 5, x_33);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
obj* l_Lean_Parser_Term_have___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_Lean_Parser_Term_have___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_2);
return x_10;
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
obj* l_Lean_Parser_Term_suffices___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_33 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_34 = lean::string_append(x_33, x_2);
x_35 = l_Char_HasRepr___closed__1;
x_36 = lean::string_append(x_34, x_35);
lean::inc(x_7);
x_37 = l_Lean_Parser_symbolFnAux(x_2, x_36, x_7, x_8);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_41 = lean::array_get_size(x_39);
lean::dec(x_39);
lean::inc(x_7);
x_42 = l_Lean_Parser_identFn___rarg(x_7, x_37);
x_43 = lean::cnstr_get(x_42, 3);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = lean::string_append(x_33, x_5);
x_45 = lean::string_append(x_44, x_35);
lean::inc(x_7);
x_46 = l_Lean_Parser_symbolFnAux(x_5, x_45, x_7, x_42);
x_47 = lean::cnstr_get(x_46, 3);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; 
lean::dec(x_40);
x_48 = l_Lean_nullKind;
x_49 = l_Lean_Parser_ParserState_mkNode(x_46, x_48, x_41);
x_11 = x_49;
goto block_32;
}
else
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_46);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_46, 0);
x_52 = lean::cnstr_get(x_46, 3);
lean::dec(x_52);
x_53 = lean::cnstr_get(x_46, 1);
lean::dec(x_53);
x_54 = l_Array_shrink___main___rarg(x_51, x_41);
lean::inc(x_40);
lean::cnstr_set(x_46, 1, x_40);
lean::cnstr_set(x_46, 0, x_54);
x_55 = lean::nat_dec_eq(x_40, x_40);
if (x_55 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_40);
x_56 = l_Lean_nullKind;
x_57 = l_Lean_Parser_ParserState_mkNode(x_46, x_56, x_41);
x_11 = x_57;
goto block_32;
}
else
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = l_Lean_Parser_ParserState_restore(x_46, x_41, x_40);
x_59 = l_Lean_nullKind;
x_60 = l_Lean_Parser_ParserState_mkNode(x_58, x_59, x_41);
x_11 = x_60;
goto block_32;
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_61 = lean::cnstr_get(x_46, 0);
x_62 = lean::cnstr_get(x_46, 2);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_46);
x_63 = l_Array_shrink___main___rarg(x_61, x_41);
lean::inc(x_40);
x_64 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_40);
lean::cnstr_set(x_64, 2, x_62);
lean::cnstr_set(x_64, 3, x_47);
x_65 = lean::nat_dec_eq(x_40, x_40);
if (x_65 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_40);
x_66 = l_Lean_nullKind;
x_67 = l_Lean_Parser_ParserState_mkNode(x_64, x_66, x_41);
x_11 = x_67;
goto block_32;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = l_Lean_Parser_ParserState_restore(x_64, x_41, x_40);
x_69 = l_Lean_nullKind;
x_70 = l_Lean_Parser_ParserState_mkNode(x_68, x_69, x_41);
x_11 = x_70;
goto block_32;
}
}
}
}
else
{
obj* x_71; 
lean::dec(x_43);
x_71 = lean::cnstr_get(x_42, 3);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_73; 
lean::dec(x_40);
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_42, x_72, x_41);
x_11 = x_73;
goto block_32;
}
else
{
uint8 x_74; 
x_74 = !lean::is_exclusive(x_42);
if (x_74 == 0)
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; uint8 x_79; 
x_75 = lean::cnstr_get(x_42, 0);
x_76 = lean::cnstr_get(x_42, 3);
lean::dec(x_76);
x_77 = lean::cnstr_get(x_42, 1);
lean::dec(x_77);
x_78 = l_Array_shrink___main___rarg(x_75, x_41);
lean::inc(x_40);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 0, x_78);
x_79 = lean::nat_dec_eq(x_40, x_40);
if (x_79 == 0)
{
obj* x_80; obj* x_81; 
lean::dec(x_40);
x_80 = l_Lean_nullKind;
x_81 = l_Lean_Parser_ParserState_mkNode(x_42, x_80, x_41);
x_11 = x_81;
goto block_32;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = l_Lean_Parser_ParserState_restore(x_42, x_41, x_40);
x_83 = l_Lean_nullKind;
x_84 = l_Lean_Parser_ParserState_mkNode(x_82, x_83, x_41);
x_11 = x_84;
goto block_32;
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; uint8 x_89; 
x_85 = lean::cnstr_get(x_42, 0);
x_86 = lean::cnstr_get(x_42, 2);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_42);
x_87 = l_Array_shrink___main___rarg(x_85, x_41);
lean::inc(x_40);
x_88 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_40);
lean::cnstr_set(x_88, 2, x_86);
lean::cnstr_set(x_88, 3, x_71);
x_89 = lean::nat_dec_eq(x_40, x_40);
if (x_89 == 0)
{
obj* x_90; obj* x_91; 
lean::dec(x_40);
x_90 = l_Lean_nullKind;
x_91 = l_Lean_Parser_ParserState_mkNode(x_88, x_90, x_41);
x_11 = x_91;
goto block_32;
}
else
{
obj* x_92; obj* x_93; obj* x_94; 
x_92 = l_Lean_Parser_ParserState_restore(x_88, x_41, x_40);
x_93 = l_Lean_nullKind;
x_94 = l_Lean_Parser_ParserState_mkNode(x_92, x_93, x_41);
x_11 = x_94;
goto block_32;
}
}
}
}
}
else
{
obj* x_95; 
lean::dec(x_38);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
x_95 = l_Lean_Parser_ParserState_mkNode(x_37, x_1, x_10);
return x_95;
}
block_32:
{
obj* x_12; 
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_14 = l_Lean_Parser_builtinTermParsingTable;
x_15 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_16 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_15, x_7, x_11);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; 
lean::inc(x_7);
x_18 = lean::apply_3(x_4, x_6, x_7, x_16);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_21 = lean::string_append(x_20, x_3);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_21, x_22);
lean::inc(x_7);
x_24 = l_Lean_Parser_symbolFnAux(x_3, x_23, x_7, x_18);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
x_26 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_15, x_7, x_24);
x_27 = l_Lean_Parser_ParserState_mkNode(x_26, x_1, x_10);
return x_27;
}
else
{
obj* x_28; 
lean::dec(x_25);
lean::dec(x_7);
x_28 = l_Lean_Parser_ParserState_mkNode(x_24, x_1, x_10);
return x_28;
}
}
else
{
obj* x_29; 
lean::dec(x_19);
lean::dec(x_7);
x_29 = l_Lean_Parser_ParserState_mkNode(x_18, x_1, x_10);
return x_29;
}
}
else
{
obj* x_30; 
lean::dec(x_17);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
x_30 = l_Lean_Parser_ParserState_mkNode(x_16, x_1, x_10);
return x_30;
}
}
else
{
obj* x_31; 
lean::dec(x_12);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
x_31 = l_Lean_Parser_ParserState_mkNode(x_11, x_1, x_10);
return x_31;
}
}
}
}
obj* _init_l_Lean_Parser_Term_suffices() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_string("; ");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_19 = l_Lean_Parser_symbolInfo(x_18, x_10);
lean::inc(x_16);
x_20 = l_Lean_Parser_andthenInfo(x_19, x_16);
x_21 = l_Lean_Parser_Term_fromTerm;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = l_Lean_Parser_andthenInfo(x_22, x_20);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
x_25 = l_Lean_Parser_andthenInfo(x_16, x_23);
x_26 = lean::mk_string("ident");
x_27 = l_Lean_Parser_mkAtomicInfo(x_26);
x_28 = lean::mk_string(" : ");
x_29 = l_String_trim(x_28);
lean::dec(x_28);
lean::inc(x_29);
x_30 = l_Lean_Parser_symbolInfo(x_29, x_10);
x_31 = l_Lean_Parser_andthenInfo(x_27, x_30);
x_32 = l_Lean_Parser_noFirstTokenInfo(x_31);
x_33 = l_Lean_Parser_andthenInfo(x_32, x_25);
x_34 = l_Lean_Parser_andthenInfo(x_13, x_33);
x_35 = l_Lean_Parser_nodeInfo(x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_suffices___elambda__1___boxed), 8, 5);
lean::closure_set(x_36, 0, x_9);
lean::closure_set(x_36, 1, x_12);
lean::closure_set(x_36, 2, x_18);
lean::closure_set(x_36, 3, x_24);
lean::closure_set(x_36, 4, x_29);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
obj* l_Lean_Parser_Term_suffices___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_suffices___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_show___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_10 = lean::string_append(x_9, x_2);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean::string_append(x_10, x_11);
lean::inc(x_5);
x_13 = l_Lean_Parser_symbolFnAux(x_2, x_12, x_5, x_6);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_16 = l_Lean_Parser_builtinTermParsingTable;
x_17 = lean::mk_nat_obj(0u);
lean::inc(x_5);
x_18 = l_Lean_Parser_runBuiltinParserUnsafe(x_15, x_16, x_17, x_5, x_13);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::apply_3(x_3, x_4, x_5, x_18);
x_21 = l_Lean_Parser_ParserState_mkNode(x_20, x_1, x_8);
return x_21;
}
else
{
obj* x_22; 
lean::dec(x_19);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_22 = l_Lean_Parser_ParserState_mkNode(x_18, x_1, x_8);
return x_22;
}
}
else
{
obj* x_23; 
lean::dec(x_14);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_23 = l_Lean_Parser_ParserState_mkNode(x_13, x_1, x_8);
return x_23;
}
}
}
obj* _init_l_Lean_Parser_Term_show() {
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
x_8 = lean::mk_string("show");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("show ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_Term_fromTerm;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = l_Lean_Parser_andthenInfo(x_16, x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
x_21 = l_Lean_Parser_andthenInfo(x_13, x_19);
x_22 = l_Lean_Parser_nodeInfo(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_show___elambda__1___boxed), 6, 3);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_12);
lean::closure_set(x_23, 2, x_20);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* l_Lean_Parser_Term_show___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Term_show___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
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
obj* l_Lean_Parser_Term_fun___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_13 = lean::string_append(x_12, x_2);
x_14 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_15 = lean::string_append(x_13, x_14);
x_16 = lean::string_append(x_15, x_3);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean::string_append(x_16, x_17);
lean::inc(x_8);
x_19 = l_Lean_Parser_unicodeSymbolFnAux(x_2, x_3, x_18, x_8, x_9);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
x_22 = lean::array_get_size(x_21);
lean::dec(x_21);
x_23 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_24 = l_Lean_Parser_builtinTermParsingTable;
x_25 = l_Lean_Parser_appPrec;
lean::inc(x_8);
x_26 = l_Lean_Parser_runBuiltinParserUnsafe(x_23, x_24, x_25, x_8, x_19);
x_27 = lean::cnstr_get(x_26, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = 0;
lean::inc(x_8);
x_29 = l_Lean_Parser_manyAux___main(x_28, x_4, x_7, x_8, x_26);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_22);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::string_append(x_12, x_5);
x_34 = lean::string_append(x_33, x_14);
x_35 = lean::string_append(x_34, x_6);
x_36 = lean::string_append(x_35, x_17);
lean::inc(x_8);
x_37 = l_Lean_Parser_unicodeSymbolFnAux(x_5, x_6, x_36, x_8, x_31);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::mk_nat_obj(0u);
x_40 = l_Lean_Parser_runBuiltinParserUnsafe(x_23, x_24, x_39, x_8, x_37);
x_41 = l_Lean_Parser_ParserState_mkNode(x_40, x_1, x_11);
return x_41;
}
else
{
obj* x_42; 
lean::dec(x_38);
lean::dec(x_8);
x_42 = l_Lean_Parser_ParserState_mkNode(x_37, x_1, x_11);
return x_42;
}
}
else
{
obj* x_43; 
lean::dec(x_32);
lean::dec(x_8);
x_43 = l_Lean_Parser_ParserState_mkNode(x_31, x_1, x_11);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_27);
lean::dec(x_7);
lean::dec(x_4);
x_44 = l_Lean_nullKind;
x_45 = l_Lean_Parser_ParserState_mkNode(x_26, x_44, x_22);
x_46 = lean::cnstr_get(x_45, 3);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_47 = lean::string_append(x_12, x_5);
x_48 = lean::string_append(x_47, x_14);
x_49 = lean::string_append(x_48, x_6);
x_50 = lean::string_append(x_49, x_17);
lean::inc(x_8);
x_51 = l_Lean_Parser_unicodeSymbolFnAux(x_5, x_6, x_50, x_8, x_45);
x_52 = lean::cnstr_get(x_51, 3);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::mk_nat_obj(0u);
x_54 = l_Lean_Parser_runBuiltinParserUnsafe(x_23, x_24, x_53, x_8, x_51);
x_55 = l_Lean_Parser_ParserState_mkNode(x_54, x_1, x_11);
return x_55;
}
else
{
obj* x_56; 
lean::dec(x_52);
lean::dec(x_8);
x_56 = l_Lean_Parser_ParserState_mkNode(x_51, x_1, x_11);
return x_56;
}
}
else
{
obj* x_57; 
lean::dec(x_46);
lean::dec(x_8);
x_57 = l_Lean_Parser_ParserState_mkNode(x_45, x_1, x_11);
return x_57;
}
}
}
else
{
obj* x_58; 
lean::dec(x_20);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
x_58 = l_Lean_Parser_ParserState_mkNode(x_19, x_1, x_11);
return x_58;
}
}
}
obj* _init_l_Lean_Parser_Term_fun() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_appPrec;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string("⇒");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
x_22 = lean::mk_string("=>");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
lean::inc(x_21);
x_24 = l_Lean_Parser_unicodeSymbolInfo(x_21, x_23, x_10);
lean::inc(x_17);
x_25 = l_Lean_Parser_andthenInfo(x_24, x_17);
x_26 = l_Lean_Parser_andthenInfo(x_17, x_25);
x_27 = l_Lean_Parser_andthenInfo(x_14, x_26);
x_28 = l_Lean_Parser_nodeInfo(x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fun___elambda__1___boxed), 9, 6);
lean::closure_set(x_29, 0, x_9);
lean::closure_set(x_29, 1, x_12);
lean::closure_set(x_29, 2, x_13);
lean::closure_set(x_29, 3, x_19);
lean::closure_set(x_29, 4, x_21);
lean::closure_set(x_29, 5, x_23);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
obj* l_Lean_Parser_Term_fun___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_Lean_Parser_Term_fun___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
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
obj* l_Lean_Parser_Term_structInstField___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
lean::inc(x_4);
x_8 = l_Lean_Parser_identFn___rarg(x_4, x_5);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_11 = lean::string_append(x_10, x_2);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_11, x_12);
lean::inc(x_4);
x_14 = l_Lean_Parser_symbolFnAux(x_2, x_13, x_4, x_8);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_17 = l_Lean_Parser_builtinTermParsingTable;
x_18 = lean::mk_nat_obj(0u);
x_19 = l_Lean_Parser_runBuiltinParserUnsafe(x_16, x_17, x_18, x_4, x_14);
x_20 = l_Lean_Parser_ParserState_mkNode(x_19, x_1, x_7);
return x_20;
}
else
{
obj* x_21; 
lean::dec(x_15);
lean::dec(x_4);
x_21 = l_Lean_Parser_ParserState_mkNode(x_14, x_1, x_7);
return x_21;
}
}
else
{
obj* x_22; 
lean::dec(x_9);
lean::dec(x_4);
x_22 = l_Lean_Parser_ParserState_mkNode(x_8, x_1, x_7);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_Term_structInstField() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
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
x_12 = lean::box(0);
x_13 = lean::mk_string(" := ");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_15 = l_Lean_Parser_symbolInfo(x_14, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_andthenInfo(x_15, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_11, x_19);
x_21 = l_Lean_Parser_nodeInfo(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInstField___elambda__1___boxed), 5, 2);
lean::closure_set(x_22, 0, x_9);
lean::closure_set(x_22, 1, x_14);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
obj* l_Lean_Parser_Term_structInstField___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_structInstField___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_structInstSource___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = lean::array_get_size(x_14);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
x_17 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_18 = l_Lean_Parser_builtinTermParsingTable;
x_19 = lean::mk_nat_obj(0u);
x_20 = l_Lean_Parser_runBuiltinParserUnsafe(x_17, x_18, x_19, x_4, x_12);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_16);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_20, x_22, x_15);
x_24 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_7);
return x_24;
}
else
{
obj* x_25; uint8 x_26; 
lean::dec(x_21);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
x_26 = lean::nat_dec_eq(x_25, x_16);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_16);
x_27 = l_Lean_nullKind;
x_28 = l_Lean_Parser_ParserState_mkNode(x_20, x_27, x_15);
x_29 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_7);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = l_Lean_Parser_ParserState_restore(x_20, x_15, x_16);
x_31 = l_Lean_nullKind;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_15);
x_33 = l_Lean_Parser_ParserState_mkNode(x_32, x_1, x_7);
return x_33;
}
}
}
else
{
obj* x_34; 
lean::dec(x_13);
lean::dec(x_4);
x_34 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_34;
}
}
}
obj* _init_l_Lean_Parser_Term_structInstSource() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_noFirstTokenInfo(x_16);
x_18 = l_Lean_Parser_andthenInfo(x_13, x_17);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInstSource___elambda__1___boxed), 5, 2);
lean::closure_set(x_20, 0, x_9);
lean::closure_set(x_20, 1, x_12);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l_Lean_Parser_Term_structInstSource___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_structInstSource___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_structInst___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_13 = lean::string_append(x_12, x_2);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean::string_append(x_13, x_14);
lean::inc(x_8);
x_16 = l_Lean_Parser_symbolFnAux(x_2, x_15, x_8, x_9);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_66; obj* x_67; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
x_20 = lean::array_get_size(x_18);
lean::dec(x_18);
lean::inc(x_8);
x_66 = l_Lean_Parser_identFn___rarg(x_8, x_16);
x_67 = lean::cnstr_get(x_66, 3);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_68 = lean::string_append(x_12, x_3);
x_69 = lean::string_append(x_68, x_14);
lean::inc(x_8);
x_70 = l_Lean_Parser_symbolFnAux(x_3, x_69, x_8, x_66);
x_71 = lean::cnstr_get(x_70, 3);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
x_21 = x_70;
goto block_65;
}
else
{
uint8 x_72; 
x_72 = !lean::is_exclusive(x_70);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_73 = lean::cnstr_get(x_70, 0);
x_74 = lean::cnstr_get(x_70, 3);
lean::dec(x_74);
x_75 = lean::cnstr_get(x_70, 1);
lean::dec(x_75);
x_76 = l_Array_shrink___main___rarg(x_73, x_20);
lean::inc(x_19);
lean::cnstr_set(x_70, 1, x_19);
lean::cnstr_set(x_70, 0, x_76);
x_21 = x_70;
goto block_65;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_70, 0);
x_78 = lean::cnstr_get(x_70, 2);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_70);
x_79 = l_Array_shrink___main___rarg(x_77, x_20);
lean::inc(x_19);
x_80 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_19);
lean::cnstr_set(x_80, 2, x_78);
lean::cnstr_set(x_80, 3, x_71);
x_21 = x_80;
goto block_65;
}
}
}
else
{
obj* x_81; 
lean::dec(x_67);
x_81 = lean::cnstr_get(x_66, 3);
lean::inc(x_81);
if (lean::obj_tag(x_81) == 0)
{
x_21 = x_66;
goto block_65;
}
else
{
uint8 x_82; 
x_82 = !lean::is_exclusive(x_66);
if (x_82 == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_83 = lean::cnstr_get(x_66, 0);
x_84 = lean::cnstr_get(x_66, 3);
lean::dec(x_84);
x_85 = lean::cnstr_get(x_66, 1);
lean::dec(x_85);
x_86 = l_Array_shrink___main___rarg(x_83, x_20);
lean::inc(x_19);
lean::cnstr_set(x_66, 1, x_19);
lean::cnstr_set(x_66, 0, x_86);
x_21 = x_66;
goto block_65;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_87 = lean::cnstr_get(x_66, 0);
x_88 = lean::cnstr_get(x_66, 2);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_66);
x_89 = l_Array_shrink___main___rarg(x_87, x_20);
lean::inc(x_19);
x_90 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_19);
lean::cnstr_set(x_90, 2, x_88);
lean::cnstr_set(x_90, 3, x_81);
x_21 = x_90;
goto block_65;
}
}
}
block_65:
{
obj* x_22; 
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_19);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_21, x_23, x_20);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; uint8 x_27; obj* x_28; obj* x_29; 
x_26 = 0;
x_27 = 1;
lean::inc(x_8);
x_28 = l_Lean_Parser_sepByFn___main(x_26, x_27, x_4, x_5, x_7, x_8, x_24);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::string_append(x_12, x_6);
x_31 = lean::string_append(x_30, x_14);
x_32 = l_Lean_Parser_symbolFnAux(x_6, x_31, x_8, x_28);
x_33 = l_Lean_Parser_ParserState_mkNode(x_32, x_1, x_11);
return x_33;
}
else
{
obj* x_34; 
lean::dec(x_29);
lean::dec(x_8);
x_34 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_11);
return x_34;
}
}
else
{
obj* x_35; 
lean::dec(x_25);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_35 = l_Lean_Parser_ParserState_mkNode(x_24, x_1, x_11);
return x_35;
}
}
else
{
obj* x_36; uint8 x_37; 
lean::dec(x_22);
x_36 = lean::cnstr_get(x_21, 1);
lean::inc(x_36);
x_37 = lean::nat_dec_eq(x_36, x_19);
lean::dec(x_36);
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_19);
x_38 = l_Lean_nullKind;
x_39 = l_Lean_Parser_ParserState_mkNode(x_21, x_38, x_20);
x_40 = lean::cnstr_get(x_39, 3);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
uint8 x_41; uint8 x_42; obj* x_43; obj* x_44; 
x_41 = 0;
x_42 = 1;
lean::inc(x_8);
x_43 = l_Lean_Parser_sepByFn___main(x_41, x_42, x_4, x_5, x_7, x_8, x_39);
x_44 = lean::cnstr_get(x_43, 3);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::string_append(x_12, x_6);
x_46 = lean::string_append(x_45, x_14);
x_47 = l_Lean_Parser_symbolFnAux(x_6, x_46, x_8, x_43);
x_48 = l_Lean_Parser_ParserState_mkNode(x_47, x_1, x_11);
return x_48;
}
else
{
obj* x_49; 
lean::dec(x_44);
lean::dec(x_8);
x_49 = l_Lean_Parser_ParserState_mkNode(x_43, x_1, x_11);
return x_49;
}
}
else
{
obj* x_50; 
lean::dec(x_40);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_50 = l_Lean_Parser_ParserState_mkNode(x_39, x_1, x_11);
return x_50;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_51 = l_Lean_Parser_ParserState_restore(x_21, x_20, x_19);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_51, x_52, x_20);
x_54 = lean::cnstr_get(x_53, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
uint8 x_55; uint8 x_56; obj* x_57; obj* x_58; 
x_55 = 0;
x_56 = 1;
lean::inc(x_8);
x_57 = l_Lean_Parser_sepByFn___main(x_55, x_56, x_4, x_5, x_7, x_8, x_53);
x_58 = lean::cnstr_get(x_57, 3);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = lean::string_append(x_12, x_6);
x_60 = lean::string_append(x_59, x_14);
x_61 = l_Lean_Parser_symbolFnAux(x_6, x_60, x_8, x_57);
x_62 = l_Lean_Parser_ParserState_mkNode(x_61, x_1, x_11);
return x_62;
}
else
{
obj* x_63; 
lean::dec(x_58);
lean::dec(x_8);
x_63 = l_Lean_Parser_ParserState_mkNode(x_57, x_1, x_11);
return x_63;
}
}
else
{
obj* x_64; 
lean::dec(x_54);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_64 = l_Lean_Parser_ParserState_mkNode(x_53, x_1, x_11);
return x_64;
}
}
}
}
}
else
{
obj* x_91; 
lean::dec(x_17);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_91 = l_Lean_Parser_ParserState_mkNode(x_16, x_1, x_11);
return x_91;
}
}
}
obj* _init_l_Lean_Parser_Term_structInst() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
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
x_15 = lean::mk_string("ident");
x_16 = l_Lean_Parser_mkAtomicInfo(x_15);
x_17 = lean::box(0);
x_18 = lean::mk_string(" . ");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = l_Lean_Parser_symbolInfo(x_19, x_17);
x_21 = l_Lean_Parser_andthenInfo(x_16, x_20);
x_22 = l_Lean_Parser_noFirstTokenInfo(x_21);
x_23 = l_Lean_Parser_Term_structInstField;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = l_Lean_Parser_Term_structInstSource;
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_27 = l_Lean_Parser_orelseInfo(x_24, x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_25, 1);
lean::inc(x_29);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::mk_string(", ");
x_32 = l_String_trim(x_31);
lean::dec(x_31);
lean::inc(x_32);
x_33 = l_Lean_Parser_symbolInfo(x_32, x_17);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_34, 0, x_32);
x_35 = l_Lean_Parser_sepByInfo(x_27, x_33);
x_36 = lean::mk_string("}");
x_37 = l_String_trim(x_36);
lean::dec(x_36);
lean::inc(x_37);
x_38 = l_Lean_Parser_symbolInfo(x_37, x_17);
x_39 = l_Lean_Parser_andthenInfo(x_35, x_38);
x_40 = l_Lean_Parser_andthenInfo(x_22, x_39);
x_41 = l_Lean_Parser_andthenInfo(x_14, x_40);
x_42 = l_Lean_Parser_nodeInfo(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInst___elambda__1___boxed), 9, 6);
lean::closure_set(x_43, 0, x_9);
lean::closure_set(x_43, 1, x_13);
lean::closure_set(x_43, 2, x_19);
lean::closure_set(x_43, 3, x_30);
lean::closure_set(x_43, 4, x_34);
lean::closure_set(x_43, 5, x_37);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
obj* l_Lean_Parser_Term_structInst___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_Lean_Parser_Term_structInst___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
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
obj* l_Lean_Parser_Term_typeSpec___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_typeSpec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_typeSpec___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_typeSpec___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_subtype___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_12 = lean::string_append(x_11, x_2);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_12, x_13);
lean::inc(x_7);
x_15 = l_Lean_Parser_symbolFnAux(x_2, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; 
lean::inc(x_7);
x_17 = l_Lean_Parser_identFn___rarg(x_7, x_15);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
lean::inc(x_7);
x_19 = lean::apply_3(x_5, x_6, x_7, x_17);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::string_append(x_11, x_3);
x_22 = lean::string_append(x_21, x_13);
lean::inc(x_7);
x_23 = l_Lean_Parser_symbolFnAux(x_3, x_22, x_7, x_19);
x_24 = lean::cnstr_get(x_23, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_26 = l_Lean_Parser_builtinTermParsingTable;
x_27 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_28 = l_Lean_Parser_runBuiltinParserUnsafe(x_25, x_26, x_27, x_7, x_23);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::string_append(x_11, x_4);
x_31 = lean::string_append(x_30, x_13);
x_32 = l_Lean_Parser_symbolFnAux(x_4, x_31, x_7, x_28);
x_33 = l_Lean_Parser_ParserState_mkNode(x_32, x_1, x_10);
return x_33;
}
else
{
obj* x_34; 
lean::dec(x_29);
lean::dec(x_7);
x_34 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_10);
return x_34;
}
}
else
{
obj* x_35; 
lean::dec(x_24);
lean::dec(x_7);
x_35 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_10);
return x_35;
}
}
else
{
obj* x_36; 
lean::dec(x_20);
lean::dec(x_7);
x_36 = l_Lean_Parser_ParserState_mkNode(x_19, x_1, x_10);
return x_36;
}
}
else
{
obj* x_37; 
lean::dec(x_18);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_37 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_10);
return x_37;
}
}
else
{
obj* x_38; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_38 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_10);
return x_38;
}
}
}
obj* _init_l_Lean_Parser_Term_subtype() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
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
x_14 = lean::mk_string("ident");
x_15 = l_Lean_Parser_mkAtomicInfo(x_14);
x_16 = lean::mk_string(" // ");
x_17 = l_String_trim(x_16);
lean::dec(x_16);
lean::inc(x_17);
x_18 = l_Lean_Parser_symbolInfo(x_17, x_10);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_20 = lean::box(1);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::mk_string("}");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_24 = l_Lean_Parser_symbolInfo(x_23, x_10);
x_25 = l_Lean_Parser_andthenInfo(x_21, x_24);
x_26 = l_Lean_Parser_andthenInfo(x_18, x_25);
x_27 = l_Lean_Parser_Term_optType;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = l_Lean_Parser_andthenInfo(x_28, x_26);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
x_31 = l_Lean_Parser_andthenInfo(x_15, x_29);
x_32 = l_Lean_Parser_andthenInfo(x_13, x_31);
x_33 = l_Lean_Parser_nodeInfo(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_subtype___elambda__1___boxed), 8, 5);
lean::closure_set(x_34, 0, x_9);
lean::closure_set(x_34, 1, x_12);
lean::closure_set(x_34, 2, x_17);
lean::closure_set(x_34, 3, x_23);
lean::closure_set(x_34, 4, x_30);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
obj* l_Lean_Parser_Term_subtype___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_subtype___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_list___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_12 = lean::string_append(x_11, x_2);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_12, x_13);
lean::inc(x_7);
x_15 = l_Lean_Parser_symbolFnAux(x_2, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; uint8 x_18; obj* x_19; obj* x_20; 
x_17 = 0;
x_18 = 1;
lean::inc(x_7);
x_19 = l_Lean_Parser_sepByFn___main(x_17, x_18, x_3, x_4, x_6, x_7, x_15);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::string_append(x_11, x_5);
x_22 = lean::string_append(x_21, x_13);
x_23 = l_Lean_Parser_symbolFnAux(x_5, x_22, x_7, x_19);
x_24 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_10);
return x_24;
}
else
{
obj* x_25; 
lean::dec(x_20);
lean::dec(x_7);
x_25 = l_Lean_Parser_ParserState_mkNode(x_19, x_1, x_10);
return x_25;
}
}
else
{
obj* x_26; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
x_26 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_10);
return x_26;
}
}
}
obj* _init_l_Lean_Parser_Term_list() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_16 = lean::box(1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::box(0);
x_21 = lean::mk_string(",");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = l_Lean_Parser_sepByInfo(x_17, x_23);
x_26 = lean::mk_string("]");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
x_28 = l_Lean_Parser_symbolInfo(x_27, x_20);
x_29 = l_Lean_Parser_andthenInfo(x_25, x_28);
x_30 = l_Lean_Parser_andthenInfo(x_14, x_29);
x_31 = l_Lean_Parser_nodeInfo(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_list___elambda__1___boxed), 8, 5);
lean::closure_set(x_32, 0, x_9);
lean::closure_set(x_32, 1, x_13);
lean::closure_set(x_32, 2, x_19);
lean::closure_set(x_32, 3, x_24);
lean::closure_set(x_32, 4, x_27);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
obj* l_Lean_Parser_Term_list___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_list___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_binderDefault___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_binderDefault() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_binderDefault___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_binderDefault___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_binderTactic___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_binderTactic() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderTactic___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_binderTactic___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_binderTactic___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_explicitBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
x_65 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_66 = lean::string_append(x_65, x_2);
x_67 = l_Char_HasRepr___closed__1;
x_68 = lean::string_append(x_66, x_67);
lean::inc(x_9);
x_69 = l_Lean_Parser_symbolFnAux(x_2, x_68, x_9, x_10);
x_70 = lean::cnstr_get(x_69, 3);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_72 = lean::array_get_size(x_71);
lean::dec(x_71);
lean::inc(x_3);
lean::inc(x_9);
lean::inc(x_8);
x_73 = lean::apply_3(x_3, x_8, x_9, x_69);
x_74 = lean::cnstr_get(x_73, 3);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
uint8 x_75; obj* x_76; obj* x_77; obj* x_78; 
x_75 = 0;
lean::inc(x_9);
lean::inc(x_8);
x_76 = l_Lean_Parser_manyAux___main(x_75, x_3, x_8, x_9, x_73);
x_77 = l_Lean_nullKind;
x_78 = l_Lean_Parser_ParserState_mkNode(x_76, x_77, x_72);
x_13 = x_78;
goto block_64;
}
else
{
obj* x_79; obj* x_80; 
lean::dec(x_74);
lean::dec(x_3);
x_79 = l_Lean_nullKind;
x_80 = l_Lean_Parser_ParserState_mkNode(x_73, x_79, x_72);
x_13 = x_80;
goto block_64;
}
}
else
{
obj* x_81; 
lean::dec(x_70);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_81 = l_Lean_Parser_ParserState_mkNode(x_69, x_1, x_12);
return x_81;
}
block_64:
{
obj* x_14; 
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
lean::inc(x_9);
lean::inc(x_8);
x_15 = lean::apply_3(x_7, x_8, x_9, x_13);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_56; obj* x_57; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::inc(x_9);
lean::inc(x_8);
x_56 = lean::apply_3(x_4, x_8, x_9, x_15);
x_57 = lean::cnstr_get(x_56, 3);
lean::inc(x_57);
if (lean::obj_tag(x_57) == 0)
{
lean::dec(x_8);
lean::dec(x_5);
x_20 = x_56;
goto block_55;
}
else
{
obj* x_58; uint8 x_59; 
lean::dec(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
x_59 = lean::nat_dec_eq(x_58, x_19);
lean::dec(x_58);
if (x_59 == 0)
{
lean::dec(x_8);
lean::dec(x_5);
x_20 = x_56;
goto block_55;
}
else
{
obj* x_60; obj* x_61; 
lean::inc(x_19);
x_60 = l_Lean_Parser_ParserState_restore(x_56, x_18, x_19);
lean::inc(x_9);
x_61 = lean::apply_3(x_5, x_8, x_9, x_60);
x_20 = x_61;
goto block_55;
}
}
block_55:
{
obj* x_21; 
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_19);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_20, x_22, x_18);
x_24 = lean::cnstr_get(x_23, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_26 = lean::string_append(x_25, x_6);
x_27 = l_Char_HasRepr___closed__1;
x_28 = lean::string_append(x_26, x_27);
x_29 = l_Lean_Parser_symbolFnAux(x_6, x_28, x_9, x_23);
x_30 = l_Lean_Parser_ParserState_mkNode(x_29, x_1, x_12);
return x_30;
}
else
{
obj* x_31; 
lean::dec(x_24);
lean::dec(x_9);
x_31 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_12);
return x_31;
}
}
else
{
obj* x_32; uint8 x_33; 
lean::dec(x_21);
x_32 = lean::cnstr_get(x_20, 1);
lean::inc(x_32);
x_33 = lean::nat_dec_eq(x_32, x_19);
lean::dec(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_19);
x_34 = l_Lean_nullKind;
x_35 = l_Lean_Parser_ParserState_mkNode(x_20, x_34, x_18);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_38 = lean::string_append(x_37, x_6);
x_39 = l_Char_HasRepr___closed__1;
x_40 = lean::string_append(x_38, x_39);
x_41 = l_Lean_Parser_symbolFnAux(x_6, x_40, x_9, x_35);
x_42 = l_Lean_Parser_ParserState_mkNode(x_41, x_1, x_12);
return x_42;
}
else
{
obj* x_43; 
lean::dec(x_36);
lean::dec(x_9);
x_43 = l_Lean_Parser_ParserState_mkNode(x_35, x_1, x_12);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = l_Lean_Parser_ParserState_restore(x_20, x_18, x_19);
x_45 = l_Lean_nullKind;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_18);
x_47 = lean::cnstr_get(x_46, 3);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_48 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_49 = lean::string_append(x_48, x_6);
x_50 = l_Char_HasRepr___closed__1;
x_51 = lean::string_append(x_49, x_50);
x_52 = l_Lean_Parser_symbolFnAux(x_6, x_51, x_9, x_46);
x_53 = l_Lean_Parser_ParserState_mkNode(x_52, x_1, x_12);
return x_53;
}
else
{
obj* x_54; 
lean::dec(x_47);
lean::dec(x_9);
x_54 = l_Lean_Parser_ParserState_mkNode(x_46, x_1, x_12);
return x_54;
}
}
}
}
}
else
{
obj* x_62; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_4);
x_62 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_12);
return x_62;
}
}
else
{
obj* x_63; 
lean::dec(x_14);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
x_63 = l_Lean_Parser_ParserState_mkNode(x_13, x_1, x_12);
return x_63;
}
}
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Term_binderDefault;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Parser_Term_binderTactic;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_orelseInfo(x_3, x_5);
x_7 = l_Lean_Parser_noFirstTokenInfo(x_6);
x_8 = lean::mk_string(")");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolInfo(x_9, x_1);
x_11 = l_Lean_Parser_andthenInfo(x_7, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_binderIdent;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("(");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__4() {
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
x_8 = lean::mk_string("explicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_binderIdent;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__7() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_binderDefault;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__8() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_binderTactic;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__9() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(")");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__10() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
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
x_15 = l_Lean_Parser_Term_explicitBinder___closed__1;
x_16 = l_Lean_Parser_andthenInfo(x_13, x_15);
x_17 = l_Lean_Parser_Term_explicitBinder___closed__2;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_16);
x_19 = l_Lean_Parser_Term_explicitBinder___closed__3;
x_20 = l_Lean_Parser_andthenInfo(x_19, x_18);
x_21 = l_Lean_Parser_nodeInfo(x_20);
x_22 = l_Lean_Parser_Term_explicitBinder___closed__4;
x_23 = l_Lean_Parser_Term_explicitBinder___closed__5;
x_24 = l_Lean_Parser_Term_explicitBinder___closed__6;
x_25 = l_Lean_Parser_Term_explicitBinder___closed__7;
x_26 = l_Lean_Parser_Term_explicitBinder___closed__8;
x_27 = l_Lean_Parser_Term_explicitBinder___closed__9;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_explicitBinder___elambda__1___boxed), 10, 7);
lean::closure_set(x_28, 0, x_22);
lean::closure_set(x_28, 1, x_23);
lean::closure_set(x_28, 2, x_24);
lean::closure_set(x_28, 3, x_25);
lean::closure_set(x_28, 4, x_26);
lean::closure_set(x_28, 5, x_27);
lean::closure_set(x_28, 6, x_14);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___closed__11() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
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
x_13 = l_Lean_Parser_Term_explicitBinder___closed__1;
x_14 = l_Lean_Parser_andthenInfo(x_11, x_13);
x_15 = l_Lean_Parser_Term_explicitBinder___closed__2;
x_16 = l_Lean_Parser_andthenInfo(x_15, x_14);
x_17 = l_Lean_Parser_Term_explicitBinder___closed__3;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_16);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = l_Lean_Parser_Term_explicitBinder___closed__4;
x_21 = l_Lean_Parser_Term_explicitBinder___closed__5;
x_22 = l_Lean_Parser_Term_explicitBinder___closed__6;
x_23 = l_Lean_Parser_Term_explicitBinder___closed__7;
x_24 = l_Lean_Parser_Term_explicitBinder___closed__8;
x_25 = l_Lean_Parser_Term_explicitBinder___closed__9;
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_explicitBinder___elambda__1___boxed), 10, 7);
lean::closure_set(x_26, 0, x_20);
lean::closure_set(x_26, 1, x_21);
lean::closure_set(x_26, 2, x_22);
lean::closure_set(x_26, 3, x_23);
lean::closure_set(x_26, 4, x_24);
lean::closure_set(x_26, 5, x_25);
lean::closure_set(x_26, 6, x_12);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_19);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
obj* l_Lean_Parser_Term_explicitBinder(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_explicitBinder___closed__10;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_explicitBinder___closed__11;
return x_3;
}
}
}
obj* l_Lean_Parser_Term_explicitBinder___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; 
x_11 = l_Lean_Parser_Term_explicitBinder___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean::dec(x_6);
lean::dec(x_2);
return x_11;
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
obj* l_Lean_Parser_Term_implicitBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_12 = lean::string_append(x_11, x_2);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_12, x_13);
lean::inc(x_7);
x_15 = l_Lean_Parser_symbolFnAux(x_2, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
lean::inc(x_3);
lean::inc(x_7);
lean::inc(x_6);
x_19 = lean::apply_3(x_3, x_6, x_7, x_15);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = 0;
lean::inc(x_7);
lean::inc(x_6);
x_22 = l_Lean_Parser_manyAux___main(x_21, x_3, x_6, x_7, x_19);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_18);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
lean::inc(x_7);
x_26 = lean::apply_3(x_5, x_6, x_7, x_24);
x_27 = lean::cnstr_get(x_26, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::string_append(x_11, x_4);
x_29 = lean::string_append(x_28, x_13);
x_30 = l_Lean_Parser_symbolFnAux(x_4, x_29, x_7, x_26);
x_31 = l_Lean_Parser_ParserState_mkNode(x_30, x_1, x_10);
return x_31;
}
else
{
obj* x_32; 
lean::dec(x_27);
lean::dec(x_7);
x_32 = l_Lean_Parser_ParserState_mkNode(x_26, x_1, x_10);
return x_32;
}
}
else
{
obj* x_33; 
lean::dec(x_25);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_33 = l_Lean_Parser_ParserState_mkNode(x_24, x_1, x_10);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_20);
lean::dec(x_3);
x_34 = l_Lean_nullKind;
x_35 = l_Lean_Parser_ParserState_mkNode(x_19, x_34, x_18);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; 
lean::inc(x_7);
x_37 = lean::apply_3(x_5, x_6, x_7, x_35);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = lean::string_append(x_11, x_4);
x_40 = lean::string_append(x_39, x_13);
x_41 = l_Lean_Parser_symbolFnAux(x_4, x_40, x_7, x_37);
x_42 = l_Lean_Parser_ParserState_mkNode(x_41, x_1, x_10);
return x_42;
}
else
{
obj* x_43; 
lean::dec(x_38);
lean::dec(x_7);
x_43 = l_Lean_Parser_ParserState_mkNode(x_37, x_1, x_10);
return x_43;
}
}
else
{
obj* x_44; 
lean::dec(x_36);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_44 = l_Lean_Parser_ParserState_mkNode(x_35, x_1, x_10);
return x_44;
}
}
}
else
{
obj* x_45; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_45 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_10);
return x_45;
}
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("}");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("{");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__3() {
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
x_8 = lean::mk_string("implicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("}");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
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
x_15 = l_Lean_Parser_Term_implicitBinder___closed__1;
x_16 = l_Lean_Parser_andthenInfo(x_13, x_15);
x_17 = l_Lean_Parser_Term_explicitBinder___closed__2;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_16);
x_19 = l_Lean_Parser_Term_implicitBinder___closed__2;
x_20 = l_Lean_Parser_andthenInfo(x_19, x_18);
x_21 = l_Lean_Parser_nodeInfo(x_20);
x_22 = l_Lean_Parser_Term_implicitBinder___closed__3;
x_23 = l_Lean_Parser_Term_implicitBinder___closed__4;
x_24 = l_Lean_Parser_Term_explicitBinder___closed__6;
x_25 = l_Lean_Parser_Term_implicitBinder___closed__5;
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_implicitBinder___elambda__1___boxed), 8, 5);
lean::closure_set(x_26, 0, x_22);
lean::closure_set(x_26, 1, x_23);
lean::closure_set(x_26, 2, x_24);
lean::closure_set(x_26, 3, x_25);
lean::closure_set(x_26, 4, x_14);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
obj* _init_l_Lean_Parser_Term_implicitBinder___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
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
x_13 = l_Lean_Parser_Term_implicitBinder___closed__1;
x_14 = l_Lean_Parser_andthenInfo(x_11, x_13);
x_15 = l_Lean_Parser_Term_explicitBinder___closed__2;
x_16 = l_Lean_Parser_andthenInfo(x_15, x_14);
x_17 = l_Lean_Parser_Term_implicitBinder___closed__2;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_16);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = l_Lean_Parser_Term_implicitBinder___closed__3;
x_21 = l_Lean_Parser_Term_implicitBinder___closed__4;
x_22 = l_Lean_Parser_Term_explicitBinder___closed__6;
x_23 = l_Lean_Parser_Term_implicitBinder___closed__5;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_implicitBinder___elambda__1___boxed), 8, 5);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_21);
lean::closure_set(x_24, 2, x_22);
lean::closure_set(x_24, 3, x_23);
lean::closure_set(x_24, 4, x_12);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* l_Lean_Parser_Term_implicitBinder(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_implicitBinder___closed__6;
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Parser_Term_implicitBinder___closed__7;
return x_3;
}
}
}
obj* l_Lean_Parser_Term_implicitBinder___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_implicitBinder___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
lean::dec(x_2);
return x_9;
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
obj* l_Lean_Parser_Term_instBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_26 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_27 = lean::string_append(x_26, x_2);
x_28 = l_Char_HasRepr___closed__1;
x_29 = lean::string_append(x_27, x_28);
lean::inc(x_6);
x_30 = l_Lean_Parser_symbolFnAux(x_2, x_29, x_6, x_7);
x_31 = lean::cnstr_get(x_30, 3);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
x_34 = lean::array_get_size(x_32);
lean::dec(x_32);
lean::inc(x_6);
x_35 = l_Lean_Parser_identFn___rarg(x_6, x_30);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = lean::string_append(x_26, x_4);
x_38 = lean::string_append(x_37, x_28);
lean::inc(x_6);
x_39 = l_Lean_Parser_symbolFnAux(x_4, x_38, x_6, x_35);
x_40 = lean::cnstr_get(x_39, 3);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_33);
x_41 = l_Lean_nullKind;
x_42 = l_Lean_Parser_ParserState_mkNode(x_39, x_41, x_34);
x_10 = x_42;
goto block_25;
}
else
{
uint8 x_43; 
x_43 = !lean::is_exclusive(x_39);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_39, 0);
x_45 = lean::cnstr_get(x_39, 3);
lean::dec(x_45);
x_46 = lean::cnstr_get(x_39, 1);
lean::dec(x_46);
x_47 = l_Array_shrink___main___rarg(x_44, x_34);
lean::inc(x_33);
lean::cnstr_set(x_39, 1, x_33);
lean::cnstr_set(x_39, 0, x_47);
x_48 = lean::nat_dec_eq(x_33, x_33);
if (x_48 == 0)
{
obj* x_49; obj* x_50; 
lean::dec(x_33);
x_49 = l_Lean_nullKind;
x_50 = l_Lean_Parser_ParserState_mkNode(x_39, x_49, x_34);
x_10 = x_50;
goto block_25;
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = l_Lean_Parser_ParserState_restore(x_39, x_34, x_33);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_51, x_52, x_34);
x_10 = x_53;
goto block_25;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_39, 0);
x_55 = lean::cnstr_get(x_39, 2);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_39);
x_56 = l_Array_shrink___main___rarg(x_54, x_34);
lean::inc(x_33);
x_57 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_33);
lean::cnstr_set(x_57, 2, x_55);
lean::cnstr_set(x_57, 3, x_40);
x_58 = lean::nat_dec_eq(x_33, x_33);
if (x_58 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_33);
x_59 = l_Lean_nullKind;
x_60 = l_Lean_Parser_ParserState_mkNode(x_57, x_59, x_34);
x_10 = x_60;
goto block_25;
}
else
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = l_Lean_Parser_ParserState_restore(x_57, x_34, x_33);
x_62 = l_Lean_nullKind;
x_63 = l_Lean_Parser_ParserState_mkNode(x_61, x_62, x_34);
x_10 = x_63;
goto block_25;
}
}
}
}
else
{
obj* x_64; 
lean::dec(x_36);
x_64 = lean::cnstr_get(x_35, 3);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_33);
x_65 = l_Lean_nullKind;
x_66 = l_Lean_Parser_ParserState_mkNode(x_35, x_65, x_34);
x_10 = x_66;
goto block_25;
}
else
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_35);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; uint8 x_72; 
x_68 = lean::cnstr_get(x_35, 0);
x_69 = lean::cnstr_get(x_35, 3);
lean::dec(x_69);
x_70 = lean::cnstr_get(x_35, 1);
lean::dec(x_70);
x_71 = l_Array_shrink___main___rarg(x_68, x_34);
lean::inc(x_33);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 0, x_71);
x_72 = lean::nat_dec_eq(x_33, x_33);
if (x_72 == 0)
{
obj* x_73; obj* x_74; 
lean::dec(x_33);
x_73 = l_Lean_nullKind;
x_74 = l_Lean_Parser_ParserState_mkNode(x_35, x_73, x_34);
x_10 = x_74;
goto block_25;
}
else
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = l_Lean_Parser_ParserState_restore(x_35, x_34, x_33);
x_76 = l_Lean_nullKind;
x_77 = l_Lean_Parser_ParserState_mkNode(x_75, x_76, x_34);
x_10 = x_77;
goto block_25;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; uint8 x_82; 
x_78 = lean::cnstr_get(x_35, 0);
x_79 = lean::cnstr_get(x_35, 2);
lean::inc(x_79);
lean::inc(x_78);
lean::dec(x_35);
x_80 = l_Array_shrink___main___rarg(x_78, x_34);
lean::inc(x_33);
x_81 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_33);
lean::cnstr_set(x_81, 2, x_79);
lean::cnstr_set(x_81, 3, x_64);
x_82 = lean::nat_dec_eq(x_33, x_33);
if (x_82 == 0)
{
obj* x_83; obj* x_84; 
lean::dec(x_33);
x_83 = l_Lean_nullKind;
x_84 = l_Lean_Parser_ParserState_mkNode(x_81, x_83, x_34);
x_10 = x_84;
goto block_25;
}
else
{
obj* x_85; obj* x_86; obj* x_87; 
x_85 = l_Lean_Parser_ParserState_restore(x_81, x_34, x_33);
x_86 = l_Lean_nullKind;
x_87 = l_Lean_Parser_ParserState_mkNode(x_85, x_86, x_34);
x_10 = x_87;
goto block_25;
}
}
}
}
}
else
{
obj* x_88; 
lean::dec(x_31);
lean::dec(x_6);
x_88 = l_Lean_Parser_ParserState_mkNode(x_30, x_1, x_9);
return x_88;
}
block_25:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinTermParsingTable;
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_6, x_10);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_18 = lean::string_append(x_17, x_3);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean::string_append(x_18, x_19);
x_21 = l_Lean_Parser_symbolFnAux(x_3, x_20, x_6, x_15);
x_22 = l_Lean_Parser_ParserState_mkNode(x_21, x_1, x_9);
return x_22;
}
else
{
obj* x_23; 
lean::dec(x_16);
lean::dec(x_6);
x_23 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_9);
return x_23;
}
}
else
{
obj* x_24; 
lean::dec(x_11);
lean::dec(x_6);
x_24 = l_Lean_Parser_ParserState_mkNode(x_10, x_1, x_9);
return x_24;
}
}
}
}
obj* _init_l_Lean_Parser_Term_instBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_string("]");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_19 = l_Lean_Parser_symbolInfo(x_18, x_10);
x_20 = l_Lean_Parser_andthenInfo(x_16, x_19);
x_21 = lean::mk_string("ident");
x_22 = l_Lean_Parser_mkAtomicInfo(x_21);
x_23 = lean::mk_string(" : ");
x_24 = l_String_trim(x_23);
lean::dec(x_23);
lean::inc(x_24);
x_25 = l_Lean_Parser_symbolInfo(x_24, x_10);
x_26 = l_Lean_Parser_andthenInfo(x_22, x_25);
x_27 = l_Lean_Parser_noFirstTokenInfo(x_26);
x_28 = l_Lean_Parser_andthenInfo(x_27, x_20);
x_29 = l_Lean_Parser_andthenInfo(x_13, x_28);
x_30 = l_Lean_Parser_nodeInfo(x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_instBinder___elambda__1___boxed), 7, 4);
lean::closure_set(x_31, 0, x_9);
lean::closure_set(x_31, 1, x_12);
lean::closure_set(x_31, 2, x_18);
lean::closure_set(x_31, 3, x_24);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
obj* l_Lean_Parser_Term_instBinder___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Term_instBinder___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
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
obj* l_Lean_Parser_Term_depArrow___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
lean::inc(x_6);
lean::inc(x_5);
x_10 = lean::apply_3(x_4, x_5, x_6, x_7);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_12 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_13 = lean::string_append(x_12, x_2);
x_14 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_15 = lean::string_append(x_13, x_14);
x_16 = lean::string_append(x_15, x_3);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean::string_append(x_16, x_17);
x_19 = l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1;
x_20 = lean::string_append(x_19, x_2);
x_21 = l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2;
x_22 = lean::string_append(x_20, x_21);
x_23 = lean::mk_nat_obj(25u);
lean::inc(x_6);
x_24 = l_Lean_Parser_unicodeSymbolCheckPrecFnAux(x_2, x_3, x_23, x_18, x_22, x_5, x_6, x_10);
lean::dec(x_5);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_27 = l_Lean_Parser_builtinTermParsingTable;
x_28 = lean::mk_nat_obj(0u);
x_29 = l_Lean_Parser_runBuiltinParserUnsafe(x_26, x_27, x_28, x_6, x_24);
x_30 = l_Lean_Parser_ParserState_mkNode(x_29, x_1, x_9);
return x_30;
}
else
{
obj* x_31; 
lean::dec(x_25);
lean::dec(x_6);
x_31 = l_Lean_Parser_ParserState_mkNode(x_24, x_1, x_9);
return x_31;
}
}
else
{
obj* x_32; 
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_5);
x_32 = l_Lean_Parser_ParserState_mkNode(x_10, x_1, x_9);
return x_32;
}
}
}
obj* _init_l_Lean_Parser_Term_depArrow() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
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
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_20 = lean::box(1);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_andthenInfo(x_18, x_21);
x_23 = lean::cnstr_get(x_11, 0);
lean::inc(x_23);
x_24 = l_Lean_Parser_andthenInfo(x_23, x_22);
x_25 = lean::cnstr_get(x_11, 1);
lean::inc(x_25);
lean::dec(x_11);
x_26 = l_Lean_Parser_nodeInfo(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_depArrow___elambda__1___boxed), 7, 4);
lean::closure_set(x_27, 0, x_9);
lean::closure_set(x_27, 1, x_13);
lean::closure_set(x_27, 2, x_15);
lean::closure_set(x_27, 3, x_25);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
obj* l_Lean_Parser_Term_depArrow___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Term_depArrow___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
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
obj* l_Lean_Parser_Term_simpleBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = lean::apply_3(x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = 0;
x_11 = l_Lean_Parser_manyAux___main(x_10, x_2, x_3, x_4, x_8);
x_12 = l_Lean_nullKind;
lean::inc(x_7);
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_7);
x_14 = l_Lean_Parser_ParserState_mkNode(x_13, x_1, x_7);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_15 = l_Lean_nullKind;
lean::inc(x_7);
x_16 = l_Lean_Parser_ParserState_mkNode(x_8, x_15, x_7);
x_17 = l_Lean_Parser_ParserState_mkNode(x_16, x_1, x_7);
return x_17;
}
}
}
obj* _init_l_Lean_Parser_Term_simpleBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_13 = l_Lean_Parser_nodeInfo(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_simpleBinder___elambda__1), 5, 2);
lean::closure_set(x_14, 0, x_9);
lean::closure_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_Lean_Parser_Term_forall___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
x_13 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_14 = lean::string_append(x_13, x_2);
x_15 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_16 = lean::string_append(x_14, x_15);
x_17 = lean::string_append(x_16, x_3);
x_18 = l_Char_HasRepr___closed__1;
x_19 = lean::string_append(x_17, x_18);
lean::inc(x_9);
x_20 = l_Lean_Parser_unicodeSymbolFnAux(x_2, x_3, x_19, x_9, x_10);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_57; obj* x_58; obj* x_59; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
x_23 = lean::array_get_size(x_22);
lean::dec(x_22);
x_57 = lean::cnstr_get(x_20, 1);
lean::inc(x_57);
lean::inc(x_9);
lean::inc(x_8);
x_58 = lean::apply_3(x_4, x_8, x_9, x_20);
x_59 = lean::cnstr_get(x_58, 3);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
lean::dec(x_57);
lean::dec(x_5);
x_24 = x_58;
goto block_56;
}
else
{
obj* x_60; uint8 x_61; 
lean::dec(x_59);
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
x_61 = lean::nat_dec_eq(x_60, x_57);
lean::dec(x_60);
if (x_61 == 0)
{
lean::dec(x_57);
lean::dec(x_5);
x_24 = x_58;
goto block_56;
}
else
{
obj* x_62; obj* x_63; 
x_62 = l_Lean_Parser_ParserState_restore(x_58, x_23, x_57);
lean::inc(x_9);
lean::inc(x_8);
x_63 = lean::apply_3(x_5, x_8, x_9, x_62);
x_24 = x_63;
goto block_56;
}
}
block_56:
{
obj* x_25; 
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = 0;
lean::inc(x_9);
x_27 = l_Lean_Parser_manyAux___main(x_26, x_6, x_8, x_9, x_24);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_23);
x_30 = lean::cnstr_get(x_29, 3);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = lean::string_append(x_13, x_7);
x_32 = lean::string_append(x_31, x_18);
lean::inc(x_9);
x_33 = l_Lean_Parser_symbolFnAux(x_7, x_32, x_9, x_29);
x_34 = lean::cnstr_get(x_33, 3);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_36 = l_Lean_Parser_builtinTermParsingTable;
x_37 = lean::mk_nat_obj(0u);
x_38 = l_Lean_Parser_runBuiltinParserUnsafe(x_35, x_36, x_37, x_9, x_33);
x_39 = l_Lean_Parser_ParserState_mkNode(x_38, x_1, x_12);
return x_39;
}
else
{
obj* x_40; 
lean::dec(x_34);
lean::dec(x_9);
x_40 = l_Lean_Parser_ParserState_mkNode(x_33, x_1, x_12);
return x_40;
}
}
else
{
obj* x_41; 
lean::dec(x_30);
lean::dec(x_9);
x_41 = l_Lean_Parser_ParserState_mkNode(x_29, x_1, x_12);
return x_41;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_25);
lean::dec(x_8);
lean::dec(x_6);
x_42 = l_Lean_nullKind;
x_43 = l_Lean_Parser_ParserState_mkNode(x_24, x_42, x_23);
x_44 = lean::cnstr_get(x_43, 3);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::string_append(x_13, x_7);
x_46 = lean::string_append(x_45, x_18);
lean::inc(x_9);
x_47 = l_Lean_Parser_symbolFnAux(x_7, x_46, x_9, x_43);
x_48 = lean::cnstr_get(x_47, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_49 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_50 = l_Lean_Parser_builtinTermParsingTable;
x_51 = lean::mk_nat_obj(0u);
x_52 = l_Lean_Parser_runBuiltinParserUnsafe(x_49, x_50, x_51, x_9, x_47);
x_53 = l_Lean_Parser_ParserState_mkNode(x_52, x_1, x_12);
return x_53;
}
else
{
obj* x_54; 
lean::dec(x_48);
lean::dec(x_9);
x_54 = l_Lean_Parser_ParserState_mkNode(x_47, x_1, x_12);
return x_54;
}
}
else
{
obj* x_55; 
lean::dec(x_44);
lean::dec(x_9);
x_55 = l_Lean_Parser_ParserState_mkNode(x_43, x_1, x_12);
return x_55;
}
}
}
}
else
{
obj* x_64; 
lean::dec(x_21);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
x_64 = l_Lean_Parser_ParserState_mkNode(x_20, x_1, x_12);
return x_64;
}
}
}
obj* _init_l_Lean_Parser_Term_forall() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
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
x_15 = 0;
x_16 = l_Lean_Parser_Term_bracktedBinder(x_15);
x_17 = l_Lean_Parser_Term_simpleBinder;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
x_20 = l_Lean_Parser_orelseInfo(x_18, x_19);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
lean::dec(x_16);
lean::inc(x_22);
lean::inc(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_22);
x_24 = lean::mk_string(", ");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_10);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_28 = lean::box(1);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_andthenInfo(x_26, x_29);
x_31 = l_Lean_Parser_andthenInfo(x_20, x_30);
x_32 = l_Lean_Parser_andthenInfo(x_14, x_31);
x_33 = l_Lean_Parser_nodeInfo(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_forall___elambda__1___boxed), 10, 7);
lean::closure_set(x_34, 0, x_9);
lean::closure_set(x_34, 1, x_12);
lean::closure_set(x_34, 2, x_13);
lean::closure_set(x_34, 3, x_21);
lean::closure_set(x_34, 4, x_22);
lean::closure_set(x_34, 5, x_23);
lean::closure_set(x_34, 6, x_25);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
obj* l_Lean_Parser_Term_forall___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; 
x_11 = l_Lean_Parser_Term_forall___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_11;
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
obj* l_Lean_Parser_Term_equation___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_12 = lean::string_append(x_11, x_2);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_12, x_13);
lean::inc(x_7);
x_15 = l_Lean_Parser_symbolFnAux(x_2, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; uint8 x_18; obj* x_19; obj* x_20; 
x_17 = 0;
x_18 = 0;
lean::inc(x_7);
x_19 = l_Lean_Parser_sepBy1Fn___main(x_17, x_18, x_3, x_4, x_6, x_7, x_15);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::string_append(x_11, x_5);
x_22 = lean::string_append(x_21, x_13);
lean::inc(x_7);
x_23 = l_Lean_Parser_symbolFnAux(x_5, x_22, x_7, x_19);
x_24 = lean::cnstr_get(x_23, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_26 = l_Lean_Parser_builtinTermParsingTable;
x_27 = lean::mk_nat_obj(0u);
x_28 = l_Lean_Parser_runBuiltinParserUnsafe(x_25, x_26, x_27, x_7, x_23);
x_29 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_10);
return x_29;
}
else
{
obj* x_30; 
lean::dec(x_24);
lean::dec(x_7);
x_30 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_10);
return x_30;
}
}
else
{
obj* x_31; 
lean::dec(x_20);
lean::dec(x_7);
x_31 = l_Lean_Parser_ParserState_mkNode(x_19, x_1, x_10);
return x_31;
}
}
else
{
obj* x_32; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
x_32 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_10);
return x_32;
}
}
}
obj* _init_l_Lean_Parser_Term_equation() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::mk_string(", ");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_20);
x_21 = l_Lean_Parser_symbolInfo(x_20, x_10);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_22, 0, x_20);
lean::inc(x_16);
x_23 = l_Lean_Parser_sepBy1Info(x_16, x_21);
x_24 = lean::mk_string(" => ");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_10);
x_27 = l_Lean_Parser_andthenInfo(x_26, x_16);
x_28 = l_Lean_Parser_andthenInfo(x_23, x_27);
x_29 = l_Lean_Parser_andthenInfo(x_13, x_28);
x_30 = l_Lean_Parser_nodeInfo(x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_equation___elambda__1___boxed), 8, 5);
lean::closure_set(x_31, 0, x_9);
lean::closure_set(x_31, 1, x_12);
lean::closure_set(x_31, 2, x_18);
lean::closure_set(x_31, 3, x_22);
lean::closure_set(x_31, 4, x_25);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
obj* l_Lean_Parser_Term_equation___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Term_equation___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_2);
return x_9;
}
}
obj* l_Lean_Parser_Term_match___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
x_13 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_14 = lean::string_append(x_13, x_2);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_14, x_15);
lean::inc(x_9);
x_17 = l_Lean_Parser_symbolFnAux(x_2, x_16, x_9, x_10);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_19 = 0;
x_20 = 0;
lean::inc(x_9);
lean::inc(x_8);
x_21 = l_Lean_Parser_sepBy1Fn___main(x_19, x_20, x_3, x_4, x_8, x_9, x_17);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; 
lean::inc(x_9);
lean::inc(x_8);
x_23 = lean::apply_3(x_7, x_8, x_9, x_21);
x_24 = lean::cnstr_get(x_23, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::string_append(x_13, x_5);
x_26 = lean::string_append(x_25, x_15);
lean::inc(x_9);
x_27 = l_Lean_Parser_symbolFnAux(x_5, x_26, x_9, x_23);
x_28 = lean::cnstr_get(x_27, 3);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_27, 0);
lean::inc(x_29);
x_30 = lean::array_get_size(x_29);
lean::dec(x_29);
lean::inc(x_6);
lean::inc(x_9);
lean::inc(x_8);
x_31 = lean::apply_3(x_6, x_8, x_9, x_27);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_33 = l_Lean_Parser_manyAux___main(x_19, x_6, x_8, x_9, x_31);
x_34 = l_Lean_nullKind;
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_30);
x_36 = l_Lean_Parser_ParserState_mkNode(x_35, x_1, x_12);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_32);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_6);
x_37 = l_Lean_nullKind;
x_38 = l_Lean_Parser_ParserState_mkNode(x_31, x_37, x_30);
x_39 = l_Lean_Parser_ParserState_mkNode(x_38, x_1, x_12);
return x_39;
}
}
else
{
obj* x_40; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_6);
x_40 = l_Lean_Parser_ParserState_mkNode(x_27, x_1, x_12);
return x_40;
}
}
else
{
obj* x_41; 
lean::dec(x_24);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_6);
x_41 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_12);
return x_41;
}
}
else
{
obj* x_42; 
lean::dec(x_22);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
x_42 = l_Lean_Parser_ParserState_mkNode(x_21, x_1, x_12);
return x_42;
}
}
else
{
obj* x_43; 
lean::dec(x_18);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
x_43 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_12);
return x_43;
}
}
}
obj* _init_l_Lean_Parser_Term_match() {
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
x_8 = lean::mk_string("match");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::mk_string("match ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParserFn___rarg___boxed), 4, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::mk_string(", ");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_20);
x_21 = l_Lean_Parser_symbolInfo(x_20, x_10);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_22, 0, x_20);
x_23 = l_Lean_Parser_sepBy1Info(x_16, x_21);
x_24 = lean::mk_string(" with ");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_10);
x_27 = l_Lean_Parser_Term_equation;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
x_30 = l_Lean_Parser_andthenInfo(x_26, x_28);
x_31 = l_Lean_Parser_Term_optType;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = l_Lean_Parser_andthenInfo(x_32, x_30);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
x_35 = l_Lean_Parser_andthenInfo(x_23, x_33);
x_36 = l_Lean_Parser_andthenInfo(x_13, x_35);
x_37 = l_Lean_Parser_nodeInfo(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_match___elambda__1___boxed), 10, 7);
lean::closure_set(x_38, 0, x_9);
lean::closure_set(x_38, 1, x_12);
lean::closure_set(x_38, 2, x_18);
lean::closure_set(x_38, 3, x_22);
lean::closure_set(x_38, 4, x_25);
lean::closure_set(x_38, 5, x_29);
lean::closure_set(x_38, 6, x_34);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
obj* l_Lean_Parser_Term_match___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; 
x_11 = l_Lean_Parser_Term_match___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean::dec(x_5);
lean::dec(x_2);
return x_11;
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
obj* l_Lean_Parser_Term_nomatch___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_16, x_4, x_12);
x_18 = l_Lean_Parser_ParserState_mkNode(x_17, x_1, x_7);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_mkNode(x_12, x_1, x_7);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_Term_nomatch() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_15 = lean::box(1);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_nomatch___elambda__1___boxed), 5, 2);
lean::closure_set(x_19, 0, x_9);
lean::closure_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_nomatch___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_nomatch___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_namedArgument___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
x_10 = lean::array_get_size(x_8);
lean::dec(x_8);
x_31 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_32 = lean::string_append(x_31, x_2);
x_33 = l_Char_HasRepr___closed__1;
x_34 = lean::string_append(x_32, x_33);
lean::inc(x_6);
x_35 = l_Lean_Parser_symbolFnAux(x_2, x_34, x_6, x_7);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; 
lean::inc(x_6);
x_37 = l_Lean_Parser_identFn___rarg(x_6, x_35);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::string_append(x_31, x_3);
x_40 = lean::string_append(x_39, x_33);
lean::inc(x_6);
x_41 = l_Lean_Parser_symbolFnAux(x_3, x_40, x_6, x_37);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_41, 3);
lean::inc(x_44);
x_11 = x_41;
x_12 = x_42;
x_13 = x_43;
x_14 = x_44;
goto block_30;
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_38);
x_45 = lean::cnstr_get(x_37, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_37, 2);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_37, 3);
lean::inc(x_47);
x_11 = x_37;
x_12 = x_45;
x_13 = x_46;
x_14 = x_47;
goto block_30;
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_36);
x_48 = lean::cnstr_get(x_35, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_35, 2);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_35, 3);
lean::inc(x_50);
x_11 = x_35;
x_12 = x_48;
x_13 = x_49;
x_14 = x_50;
goto block_30;
}
block_30:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_9);
x_15 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_16 = l_Lean_Parser_builtinTermParsingTable;
x_17 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_18 = l_Lean_Parser_runBuiltinParserUnsafe(x_15, x_16, x_17, x_6, x_11);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_21 = lean::string_append(x_20, x_4);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_21, x_22);
x_24 = l_Lean_Parser_symbolFnAux(x_4, x_23, x_6, x_18);
x_25 = l_Lean_Parser_ParserState_mkNode(x_24, x_1, x_10);
return x_25;
}
else
{
obj* x_26; 
lean::dec(x_19);
lean::dec(x_6);
x_26 = l_Lean_Parser_ParserState_mkNode(x_18, x_1, x_10);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_11);
lean::dec(x_6);
x_27 = l_Array_shrink___main___rarg(x_12, x_10);
x_28 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_13);
lean::cnstr_set(x_28, 3, x_14);
x_29 = l_Lean_Parser_ParserState_mkNode(x_28, x_1, x_10);
return x_29;
}
}
}
}
obj* _init_l_Lean_Parser_Term_namedArgument() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
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
x_14 = lean::mk_string("ident");
x_15 = l_Lean_Parser_mkAtomicInfo(x_14);
x_16 = lean::mk_string(" := ");
x_17 = l_String_trim(x_16);
lean::dec(x_16);
lean::inc(x_17);
x_18 = l_Lean_Parser_symbolInfo(x_17, x_10);
x_19 = l_Lean_Parser_andthenInfo(x_15, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_13, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_22 = lean::box(1);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::mk_string(")");
x_25 = l_String_trim(x_24);
lean::dec(x_24);
lean::inc(x_25);
x_26 = l_Lean_Parser_symbolInfo(x_25, x_10);
x_27 = l_Lean_Parser_andthenInfo(x_23, x_26);
x_28 = l_Lean_Parser_andthenInfo(x_20, x_27);
x_29 = l_Lean_Parser_nodeInfo(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_namedArgument___elambda__1___boxed), 7, 4);
lean::closure_set(x_30, 0, x_9);
lean::closure_set(x_30, 1, x_12);
lean::closure_set(x_30, 2, x_17);
lean::closure_set(x_30, 3, x_25);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
obj* l_Lean_Parser_Term_namedArgument___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Term_namedArgument___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_Parser_Term_app___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
lean::inc(x_3);
lean::inc(x_5);
x_8 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_3);
x_9 = lean::cnstr_get(x_5, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_4);
x_13 = lean::apply_3(x_2, x_3, x_4, x_8);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_4);
x_15 = l_Lean_Parser_ParserState_mkNode(x_13, x_1, x_7);
return x_15;
}
else
{
obj* x_16; uint8 x_17; 
lean::dec(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_17 = lean::nat_dec_eq(x_16, x_12);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_4);
x_18 = l_Lean_Parser_ParserState_mkNode(x_13, x_1, x_7);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
lean::dec(x_11);
x_20 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_21 = l_Lean_Parser_builtinTermParsingTable;
x_22 = l_Lean_Parser_appPrec;
x_23 = l_Lean_Parser_runBuiltinParserUnsafe(x_20, x_21, x_22, x_4, x_19);
x_24 = l_Lean_Parser_ParserState_mkNode(x_23, x_1, x_7);
return x_24;
}
}
}
else
{
obj* x_25; 
lean::dec(x_9);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_25 = l_Lean_Parser_ParserState_mkNode(x_8, x_1, x_7);
return x_25;
}
}
}
obj* _init_l_Lean_Parser_Term_app() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
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
x_13 = l_Lean_Parser_Term_namedArgument;
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = l_Lean_Parser_orelseInfo(x_14, x_12);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_17 = l_Lean_Parser_epsilonInfo;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_15);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_app___elambda__1), 5, 2);
lean::closure_set(x_20, 0, x_9);
lean::closure_set(x_20, 1, x_16);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
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
obj* l_Lean_Parser_Term_proj___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
lean::inc(x_3);
lean::inc(x_5);
x_8 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_3);
x_9 = lean::cnstr_get(x_5, 3);
lean::inc(x_9);
lean::dec(x_5);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_11 = lean::string_append(x_10, x_2);
x_12 = l_Lean_Parser_symbolNoWsFn___closed__1;
x_13 = lean::string_append(x_11, x_12);
x_14 = l_Lean_Parser_checkTailNoWs(x_3);
lean::dec(x_3);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = l_Lean_Parser_ParserState_mkError(x_8, x_13);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_20 = l_Lean_Parser_fieldIdxFn(x_4, x_15);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
lean::dec(x_19);
lean::dec(x_18);
lean::dec(x_4);
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_1, x_7);
return x_22;
}
else
{
obj* x_23; uint8 x_24; 
lean::dec(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
x_24 = lean::nat_dec_eq(x_23, x_19);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_19);
lean::dec(x_18);
lean::dec(x_4);
x_25 = l_Lean_Parser_ParserState_mkNode(x_20, x_1, x_7);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_Lean_Parser_ParserState_restore(x_20, x_18, x_19);
lean::dec(x_18);
x_27 = l_Lean_Parser_identFn___rarg(x_4, x_26);
x_28 = l_Lean_Parser_ParserState_mkNode(x_27, x_1, x_7);
return x_28;
}
}
}
else
{
obj* x_29; 
lean::dec(x_16);
lean::dec(x_4);
x_29 = l_Lean_Parser_ParserState_mkNode(x_15, x_1, x_7);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::mk_nat_obj(0u);
x_31 = l_Lean_Parser_strAux___main(x_2, x_13, x_30, x_4, x_8);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
x_34 = lean::array_get_size(x_33);
lean::dec(x_33);
x_35 = lean::cnstr_get(x_31, 1);
lean::inc(x_35);
x_36 = l_Lean_Parser_fieldIdxFn(x_4, x_31);
x_37 = lean::cnstr_get(x_36, 3);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
lean::dec(x_35);
lean::dec(x_34);
lean::dec(x_4);
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_1, x_7);
return x_38;
}
else
{
obj* x_39; uint8 x_40; 
lean::dec(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
x_40 = lean::nat_dec_eq(x_39, x_35);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_41; 
lean::dec(x_35);
lean::dec(x_34);
lean::dec(x_4);
x_41 = l_Lean_Parser_ParserState_mkNode(x_36, x_1, x_7);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = l_Lean_Parser_ParserState_restore(x_36, x_34, x_35);
lean::dec(x_34);
x_43 = l_Lean_Parser_identFn___rarg(x_4, x_42);
x_44 = l_Lean_Parser_ParserState_mkNode(x_43, x_1, x_7);
return x_44;
}
}
}
else
{
obj* x_45; 
lean::dec(x_32);
lean::dec(x_4);
x_45 = l_Lean_Parser_ParserState_mkNode(x_31, x_1, x_7);
return x_45;
}
}
}
else
{
obj* x_46; 
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_3);
x_46 = l_Lean_Parser_ParserState_mkNode(x_8, x_1, x_7);
return x_46;
}
}
}
obj* _init_l_Lean_Parser_Term_proj() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
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
x_17 = lean::mk_string("fieldIdx");
x_18 = l_Lean_Parser_mkAtomicInfo(x_17);
x_19 = lean::mk_string("ident");
x_20 = l_Lean_Parser_mkAtomicInfo(x_19);
x_21 = l_Lean_Parser_orelseInfo(x_18, x_20);
x_22 = l_Lean_Parser_andthenInfo(x_16, x_21);
x_23 = l_Lean_Parser_epsilonInfo;
x_24 = l_Lean_Parser_andthenInfo(x_23, x_22);
x_25 = l_Lean_Parser_nodeInfo(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_proj___elambda__1___boxed), 5, 2);
lean::closure_set(x_26, 0, x_9);
lean::closure_set(x_26, 1, x_15);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
obj* l_Lean_Parser_Term_proj___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_proj___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
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
obj* l_Lean_Parser_Term_arrow___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_arrow() {
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_arrow___elambda__1), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* l_Lean_Parser_Term_array___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
lean::inc(x_4);
lean::inc(x_6);
x_9 = l_Lean_Parser_ParserState_pushSyntax(x_6, x_4);
x_10 = lean::cnstr_get(x_6, 3);
lean::inc(x_10);
lean::dec(x_6);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_11 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_12 = lean::string_append(x_11, x_2);
x_13 = l_Lean_Parser_symbolNoWsFn___closed__1;
x_14 = lean::string_append(x_12, x_13);
x_15 = l_Lean_Parser_checkTailNoWs(x_4);
lean::dec(x_4);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_Lean_Parser_ParserState_mkError(x_9, x_14);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_19 = l_Lean_Parser_builtinTermParsingTable;
x_20 = lean::mk_nat_obj(0u);
lean::inc(x_5);
x_21 = l_Lean_Parser_runBuiltinParserUnsafe(x_18, x_19, x_20, x_5, x_16);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::string_append(x_11, x_3);
x_24 = l_Char_HasRepr___closed__1;
x_25 = lean::string_append(x_23, x_24);
x_26 = l_Lean_Parser_symbolFnAux(x_3, x_25, x_5, x_21);
x_27 = l_Lean_Parser_ParserState_mkNode(x_26, x_1, x_8);
return x_27;
}
else
{
obj* x_28; 
lean::dec(x_22);
lean::dec(x_5);
x_28 = l_Lean_Parser_ParserState_mkNode(x_21, x_1, x_8);
return x_28;
}
}
else
{
obj* x_29; 
lean::dec(x_17);
lean::dec(x_5);
x_29 = l_Lean_Parser_ParserState_mkNode(x_16, x_1, x_8);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::mk_nat_obj(0u);
x_31 = l_Lean_Parser_strAux___main(x_2, x_14, x_30, x_5, x_9);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_33 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_34 = l_Lean_Parser_builtinTermParsingTable;
lean::inc(x_5);
x_35 = l_Lean_Parser_runBuiltinParserUnsafe(x_33, x_34, x_30, x_5, x_31);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = lean::string_append(x_11, x_3);
x_38 = l_Char_HasRepr___closed__1;
x_39 = lean::string_append(x_37, x_38);
x_40 = l_Lean_Parser_symbolFnAux(x_3, x_39, x_5, x_35);
x_41 = l_Lean_Parser_ParserState_mkNode(x_40, x_1, x_8);
return x_41;
}
else
{
obj* x_42; 
lean::dec(x_36);
lean::dec(x_5);
x_42 = l_Lean_Parser_ParserState_mkNode(x_35, x_1, x_8);
return x_42;
}
}
else
{
obj* x_43; 
lean::dec(x_32);
lean::dec(x_5);
x_43 = l_Lean_Parser_ParserState_mkNode(x_31, x_1, x_8);
return x_43;
}
}
}
else
{
obj* x_44; 
lean::dec(x_10);
lean::dec(x_5);
lean::dec(x_4);
x_44 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_44;
}
}
}
obj* _init_l_Lean_Parser_Term_array() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
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
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_18 = lean::box(1);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::box(0);
x_21 = lean::mk_string("]");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = l_Lean_Parser_symbolInfo(x_22, x_20);
x_24 = l_Lean_Parser_andthenInfo(x_19, x_23);
x_25 = l_Lean_Parser_andthenInfo(x_16, x_24);
x_26 = l_Lean_Parser_epsilonInfo;
x_27 = l_Lean_Parser_andthenInfo(x_26, x_25);
x_28 = l_Lean_Parser_nodeInfo(x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_array___elambda__1___boxed), 6, 3);
lean::closure_set(x_29, 0, x_9);
lean::closure_set(x_29, 1, x_15);
lean::closure_set(x_29, 2, x_22);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
obj* l_Lean_Parser_Term_array___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Term_array___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
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
obj* l_Lean_Parser_Term_fcomp___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_fcomp() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fcomp___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_add___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_add() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_add___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_sub___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_sub() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sub___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_mul___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_mul() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_mul___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_div___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_div() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_div___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_mod___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_mod() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_mod___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_modN___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_modN() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_modN___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_le___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_le() {
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_le___elambda__1), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* l_Lean_Parser_Term_ge___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_ge() {
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_ge___elambda__1), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* l_Lean_Parser_Term_lt___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_lt() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_lt___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_gt___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_gt() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_gt___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_eq___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_eq() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_eq___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_beq___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_beq() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_beq___elambda__1), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* l_Lean_Parser_Term_and___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_and() {
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_and___elambda__1), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* l_Lean_Parser_Term_or___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_or() {
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_or___elambda__1), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* l_Lean_Parser_Term_iff___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::apply_3(x_6, x_3, x_4, x_5);
x_10 = l_Lean_Parser_ParserState_mkNode(x_9, x_1, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_iff() {
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_iff___elambda__1), 5, 2);
lean::closure_set(x_16, 0, x_9);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
l_Lean_Parser_Term_explicitBinder___closed__3 = _init_l_Lean_Parser_Term_explicitBinder___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__3);
l_Lean_Parser_Term_explicitBinder___closed__4 = _init_l_Lean_Parser_Term_explicitBinder___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__4);
l_Lean_Parser_Term_explicitBinder___closed__5 = _init_l_Lean_Parser_Term_explicitBinder___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__5);
l_Lean_Parser_Term_explicitBinder___closed__6 = _init_l_Lean_Parser_Term_explicitBinder___closed__6();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__6);
l_Lean_Parser_Term_explicitBinder___closed__7 = _init_l_Lean_Parser_Term_explicitBinder___closed__7();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__7);
l_Lean_Parser_Term_explicitBinder___closed__8 = _init_l_Lean_Parser_Term_explicitBinder___closed__8();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__8);
l_Lean_Parser_Term_explicitBinder___closed__9 = _init_l_Lean_Parser_Term_explicitBinder___closed__9();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__9);
l_Lean_Parser_Term_explicitBinder___closed__10 = _init_l_Lean_Parser_Term_explicitBinder___closed__10();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__10);
l_Lean_Parser_Term_explicitBinder___closed__11 = _init_l_Lean_Parser_Term_explicitBinder___closed__11();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__11);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "explicitBinder"), 1, l_Lean_Parser_Term_explicitBinder___boxed);
l_Lean_Parser_Term_implicitBinder___closed__1 = _init_l_Lean_Parser_Term_implicitBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__1);
l_Lean_Parser_Term_implicitBinder___closed__2 = _init_l_Lean_Parser_Term_implicitBinder___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__2);
l_Lean_Parser_Term_implicitBinder___closed__3 = _init_l_Lean_Parser_Term_implicitBinder___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__3);
l_Lean_Parser_Term_implicitBinder___closed__4 = _init_l_Lean_Parser_Term_implicitBinder___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__4);
l_Lean_Parser_Term_implicitBinder___closed__5 = _init_l_Lean_Parser_Term_implicitBinder___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__5);
l_Lean_Parser_Term_implicitBinder___closed__6 = _init_l_Lean_Parser_Term_implicitBinder___closed__6();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__6);
l_Lean_Parser_Term_implicitBinder___closed__7 = _init_l_Lean_Parser_Term_implicitBinder___closed__7();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__7);
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
