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
obj* l_Lean_Parser_Term_sorry___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_simpleBinder___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_arrow___elambda__1___closed__1;
obj* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3;
uint8 l_Lean_Parser_checkTailNoWs(obj*);
obj* l_Lean_Parser_Term_lt___elambda__1___closed__1;
obj* l_Lean_Parser_Term_arrow;
obj* l_Lean_Parser_Term_structInstSource;
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj*);
obj* l_Lean_Parser_Term_subtype___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_add___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser(uint8, obj*);
obj* l_Lean_Parser_Term_tupleTail___elambda__1___closed__1;
obj* l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_hole___elambda__1___boxed(obj*);
obj* l_Lean_Parser_strLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_num;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_match___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__2(obj*, uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_app___elambda__1___closed__1;
obj* l_Lean_Parser_Term_optType;
obj* l_Lean_Parser_Term_subtype___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1___closed__6;
obj* l_Lean_Parser_Term_nomatch___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_namedArgument;
obj* l_Lean_Parser_Term_array;
obj* l_Lean_Parser_Term_fun___elambda__1___closed__6;
obj* l_Lean_Parser_Term_have___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_show___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_list___elambda__1___closed__3;
obj* l_Lean_Parser_Term_hole___elambda__1(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Term_unicodeInfixL(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_optIdent___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_structInst___elambda__1___closed__2;
obj* l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
extern obj* l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
obj* l_Lean_Parser_Term_sorry___elambda__1___boxed(obj*);
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_fromTerm;
obj* l_Lean_Parser_Term_binderTactic___elambda__1___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_add(obj*);
obj* l_Lean_Parser_Term_haveAssign___elambda__1(obj*);
obj* l_Lean_Parser_Term_id___elambda__1___closed__4;
obj* l_Lean_Parser_Term_array___elambda__1___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_forall(obj*);
obj* l_Lean_Parser_Term_infixR___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_le;
obj* l_Lean_Parser_Term_show___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_mod___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_equation___elambda__1___closed__5;
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_Term_nomatch___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_binderIdent___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_sub___elambda__1___closed__1;
obj* l_Lean_Parser_Term_infixL___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_list___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_cdot___elambda__1___boxed(obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_parenSpecial;
obj* l_Lean_Parser_Term_suffices___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1___closed__3;
obj* l_Lean_Parser_Term_add___elambda__1___closed__1;
obj* l_Lean_Parser_Term_and;
obj* l_Lean_Parser_Term_hole;
obj* l_Lean_Parser_termParserFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_have;
obj* l_Lean_Parser_Term_modN;
obj* l_Lean_Parser_Term_sort___elambda__1(obj*);
obj* l_Lean_Parser_Term_equation___elambda__1___closed__1;
obj* l_Lean_Parser_Term_optIdent___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_beq___elambda__1___closed__1;
obj* l_Lean_Parser_Term_namedArgument___elambda__1(obj*);
obj* l_Lean_Parser_Term_equation___elambda__1___closed__4;
obj* l_Lean_Parser_Term_subtype___elambda__1(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___elambda__1___spec__2(obj*, uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType___closed__2;
obj* l_Lean_Parser_Term_binderIdent___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_forall___elambda__1___closed__3;
obj* l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_if(obj*);
obj* l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_fun(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp(obj*);
obj* l_Lean_Parser_Term_binderType___elambda__2(obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
obj* l_Lean_Parser_Term_type___elambda__1(obj*);
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
obj* l_Lean_Parser_Term_infixR___elambda__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
extern obj* l_Lean_Parser_builtinLevelParsingTable;
obj* l_Lean_Parser_builtinTermParsingTable;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_fun___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj*);
obj* l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj*);
obj* l_Lean_Parser_Term_binderType___closed__1;
obj* l_Lean_Parser_Term_unicodeInfixR___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1___closed__1;
obj* l_Lean_Parser_Term_tupleTail;
obj* l_Lean_Parser_Term_paren___elambda__1___closed__1;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(obj*, uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInst___elambda__1___closed__3;
obj* l_Lean_Parser_Term_parenSpecial___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_type___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_typeAscription___elambda__1___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_app___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_tupleTail___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_namedArgument___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_div___elambda__1___closed__1;
obj* l_Lean_Parser_Term_and___elambda__1___closed__1;
obj* l_Lean_Parser_Term_infixR(obj*, obj*);
obj* l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_fcomp___elambda__1___closed__1;
extern obj* l_Lean_Parser_appPrec;
obj* l_Lean_Parser_Term_binderTactic;
extern obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___elambda__1___spec__1(obj*, uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_sub___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_tupleTail___elambda__1___boxed(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(obj*);
obj* l_Lean_Parser_Term_binderType___elambda__2___rarg(obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInst___elambda__1___closed__5;
obj* l_Lean_Parser_Term_beq;
obj* l_Lean_Parser_Term_suffices;
extern obj* l_Lean_Parser_symbolFn___rarg___closed__1;
obj* l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_mul___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1___closed__3;
obj* l_Lean_Parser_Term_explicitBinder___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder(uint8);
obj* l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_sub;
obj* l_Lean_Parser_Term_mul;
obj* l_Lean_Parser_Term_structInstField___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_match___elambda__1___closed__2;
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_list___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1___closed__4;
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_Lean_Parser_termParserFn___rarg___closed__1;
obj* l_Lean_Parser_Term_unicodeInfixL___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_Term_id___elambda__1___closed__5;
obj* l_Lean_Parser_Term_arrow___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_show___elambda__1(obj*);
obj* l_Lean_Parser_Term_have___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_ge___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_eq___elambda__1___closed__1;
obj* l_Lean_Parser_Term_structInstSource___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_implicitBinder___closed__2;
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__6;
obj* l_Lean_Parser_Term_structInst;
obj* l_Lean_Parser_Term_le___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_type___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_infixL(obj*, obj*);
obj* l_Lean_Parser_Term_str;
obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_modN___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_fieldIdxFn(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_modN(obj*);
obj* l_Lean_Parser_Term_equation;
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5;
obj* l_Lean_Parser_Term_proj___elambda__1___closed__1;
obj* l_Lean_Parser_Term_namedArgument___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_id;
obj* l_Lean_Parser_Term_equation___elambda__1___closed__2;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2(obj*, uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_structInst___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_add;
obj* l_Lean_Parser_Term_type___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_haveAssign;
obj* l___regBuiltinParser_Lean_Parser_Term_proj(obj*);
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_str(obj*);
obj* l_Lean_Parser_Term_depArrow;
obj* l_Lean_Parser_Term_list___elambda__1___closed__4;
obj* l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_list___elambda__1___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_le(obj*);
obj* l_Lean_Parser_Term_binderDefault___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_fcomp;
obj* l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_suffices(obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
obj* l_Lean_Parser_Term_typeSpec___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_binderIdent;
obj* l_Lean_Parser_Term_structInstField___elambda__1(obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_unicodeInfixR(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType(uint8);
extern obj* l_Lean_Parser_manyAux___main___closed__1;
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_eq(obj*);
obj* l_Lean_Parser_Term_paren___elambda__1(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Term_fun___elambda__1___closed__1;
obj* l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_nomatch___elambda__1(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_array(obj*);
obj* l_Lean_Parser_Term_if;
obj* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
obj* l___regBuiltinParser_Lean_Parser_Term_iff(obj*);
obj* l_Lean_Parser_Term_proj___elambda__1___closed__3;
obj* l_Lean_Parser_termParserFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_or___elambda__1___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_str___closed__1;
obj* l_Lean_Parser_Term_typeSpec___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_eq___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_iff;
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj*);
obj* l_Lean_Parser_Term_typeAscription___elambda__1(obj*);
obj* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_fun___elambda__1___closed__5;
obj* l_Lean_Parser_Term_match___elambda__1___closed__3;
obj* l_Lean_Parser_Term_simpleBinder;
obj* l_Lean_Parser_Term_binderType___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
obj* l_Lean_Parser_Term_infixR___elambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_suffices___elambda__1(obj*);
obj* l_Lean_Parser_Term_mod___elambda__1___closed__1;
obj* l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_list___elambda__1___closed__5;
obj* l_Lean_Parser_Term_list___elambda__1___closed__6;
obj* l_Lean_Parser_Term_structInst___elambda__1___closed__1;
obj* l_Lean_Parser_Term_sort___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__3;
obj* l_Lean_Parser_Term_match___elambda__1___closed__4;
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_Term_cdot;
obj* l_Lean_Parser_Term_gt;
obj* l_Lean_Parser_Term_structInst___elambda__1___closed__4;
obj* l_Lean_Parser_Term_paren;
obj* l___regBuiltinParser_Lean_Parser_Term_sorry(obj*);
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__4;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Term_list___elambda__1___closed__2;
obj* l_Lean_Parser_Term_sort;
obj* l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Term_infixL___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_gt___elambda__1(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_match(obj*);
obj* l_Lean_Parser_Term_fun___elambda__1___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_Term_fromTerm___elambda__1(obj*);
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_Term_sorry;
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_match;
obj* l_Lean_Parser_Term_have___elambda__1___rarg___closed__1;
extern obj* l_Lean_Parser_levelParserFn___rarg___closed__1;
obj* l_Lean_Parser_Term_iff___elambda__1___closed__1;
obj* l_Lean_Parser_Term_explicitBinder___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Term_fcomp___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderType___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_fun___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInst___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_fun___elambda__1___closed__4;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___elambda__1___spec__1(obj*, uint8, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_structInst(obj*);
obj* l_Lean_Parser_Term_optIdent___elambda__1(obj*);
obj* l_Lean_Parser_Term_show___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_depArrow___elambda__1___closed__5;
obj* l_Lean_Parser_Term_fromTerm___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1;
extern obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_unicodeInfixL___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_parenSpecial___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_paren___elambda__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_show___elambda__1___rarg(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num___closed__1;
obj* l_Lean_Parser_Term_have___elambda__1(obj*);
obj* l_Lean_Parser_Term_depArrow___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolCheckPrecFnAux(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_have___elambda__1___boxed(obj*);
obj* l_Lean_Parser_strAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_equation___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_subtype;
obj* l_Lean_Parser_Term_infixL___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_if___elambda__1(obj*);
obj* l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_forall;
obj* l_Lean_Parser_Term_match___elambda__1___closed__1;
obj* l_Lean_Parser_Term_ge___elambda__1___closed__1;
obj* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
obj* l_Lean_Parser_Term_explicitBinder___closed__3;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_and(obj*);
obj* l_Lean_Parser_Term_mod;
obj* l_Lean_Parser_Term_proj;
obj* l_Lean_Parser_Term_forall___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__4;
extern obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj*);
obj* l_Lean_Parser_Term_equation___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_sub(obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_nomatch(obj*);
obj* l_Lean_Parser_Term_explicitBinder___closed__2;
obj* l_Lean_Parser_Term_fun___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_iff___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_match___elambda__1(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_id(obj*);
obj* l_Lean_Parser_Term_binderIdent___elambda__1(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow(obj*);
obj* l_Lean_Parser_Term_if___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_instBinder___elambda__1(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_div(obj*);
obj* l_Lean_Parser_Term_optType___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_unicodeInfixL___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj*);
obj* l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_match___elambda__1___closed__5;
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_unicodeInfixR___boxed(obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_match___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_or;
obj* l_Lean_Parser_Term_id___elambda__1___closed__2;
obj* l_Lean_Parser_Term_simpleBinder___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderDefault;
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_show;
obj* l_Lean_Parser_Term_explicitBinder(uint8);
obj* l_Lean_Parser_Term_instBinder___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1;
obj* l_Lean_Parser_symbolNoWsInfo(obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_or(obj*);
obj* l_Lean_Parser_Term_fun___elambda__1___closed__7;
obj* l_Lean_Parser_Term_instBinder;
obj* l___regBuiltinParser_Lean_Parser_Term_arrow(obj*);
obj* l_Lean_Parser_Term_div___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_lt___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkError(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_have(obj*);
obj* l_Lean_Parser_Term_list;
obj* l_Lean_Parser_Term_gt___elambda__1___closed__1;
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Lean_Parser_Term_proj___elambda__1___closed__2;
obj* l_Lean_Parser_Term_implicitBinder___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_proj___elambda__1(obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_Term_binderTactic___elambda__1(obj*);
obj* l_Lean_Parser_Term_fromTerm___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_binderType___elambda__2___boxed(obj*);
obj* l_Lean_Parser_Term_typeAscription;
obj* l_Lean_Parser_Term_binderTactic___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_termParserFn(uint8);
obj* l_Lean_Parser_Term_unicodeInfixR___elambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInstSource___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_show___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
obj* l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_cdot___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_optType___elambda__1___rarg(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj*);
obj* l_Lean_Parser_Term_beq___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_hole___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_implicitBinder___boxed(obj*);
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
obj* l_Lean_Parser_Term_have___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_forall___elambda__1___closed__5;
obj* l_Lean_Parser_Term_bracktedBinder(uint8);
obj* l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_sort___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_optType___elambda__1(obj*);
obj* l_Lean_Parser_Term_forall___elambda__1___closed__2;
obj* l_Lean_Parser_Term_optIdent;
obj* l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_show(obj*);
obj* l_Lean_Parser_Term_array___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_termParserFn___boxed(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_beq(obj*);
obj* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
obj* l_Lean_Parser_Term_match___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_id___elambda__1___closed__1;
obj* l_Lean_Parser_Term_instBinder___elambda__1___rarg(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_list(obj*);
obj* l_Lean_Parser_Term_explicitBinder___boxed(obj*);
obj* l_Lean_Parser_Term_binderType___elambda__1(obj*);
obj* l_Lean_Parser_Term_nomatch;
obj* l_Lean_Parser_Term_forall___elambda__1___closed__4;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___elambda__1___spec__2(obj*, uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_ge(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_num(obj*);
obj* l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_le___elambda__1___closed__1;
obj* l_Lean_Parser_Term_typeAscription___elambda__1___boxed(obj*);
obj* l_Lean_Parser_unicodeSymbolInfo(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_type;
obj* l___regBuiltinParser_Lean_Parser_Term_subtype(obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mod(obj*);
obj* l_Lean_Parser_Term_haveAssign___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_structInstField___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_modN___elambda__1___closed__1;
obj* l_Lean_Parser_Term_binderType___boxed(obj*);
obj* l_Lean_Parser_Term_anonymousCtor;
obj* l_Lean_Parser_Term_implicitBinder___closed__1;
obj* l_Lean_Parser_Term_binderDefault___elambda__1(obj*);
extern obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_Term_bracktedBinder___closed__1;
obj* l_Lean_Parser_Term_eq;
obj* l_Lean_Parser_Term_sorry___elambda__1(obj*);
obj* l_Lean_Parser_Term_typeSpec___elambda__1(obj*);
obj* l_Lean_Parser_Term_equation___elambda__1___closed__3;
obj* l_Lean_Parser_Term_or___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_bracktedBinder___boxed(obj*);
obj* l_Lean_Parser_Term_structInstField;
obj* l_Lean_Parser_Term_binderDefault___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_forall___elambda__1___closed__1;
obj* l_Lean_Parser_Term_have___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_Term_if___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_array___elambda__1___closed__1;
obj* l___regBuiltinParser_Lean_Parser_Term_gt(obj*);
obj* l_Lean_Parser_Term_div;
obj* l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1(obj*, uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_mul___elambda__1___closed__1;
obj* l_Lean_Parser_Term_suffices___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_if___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Term_typeSpec;
obj* l_Lean_Parser_Term_bracktedBinder___elambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_structInstSource___elambda__1(obj*);
obj* l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Term_ge;
extern obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Term_fun;
obj* l_Lean_Parser_Term_fun___elambda__1___closed__2;
obj* l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Term_type___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_and___elambda__1(obj*, obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_mul(obj*);
obj* l_Lean_Parser_Term_cdot___elambda__1(obj*);
obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Term_fun___elambda__1___closed__3;
obj* l_Lean_Parser_sepByInfo(obj*, obj*);
obj* l___regBuiltinParser_Lean_Parser_Term_lt(obj*);
obj* l_Lean_Parser_Term_lt;
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* l_Lean_Parser_Term_app;
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
obj* l_Lean_Parser_Term_unicodeInfixR___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_6);
x_7 = l_Lean_Parser_ParserState_pushSyntax(x_6, x_4);
x_8 = lean::cnstr_get(x_6, 3);
lean::inc(x_8);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_9 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_10 = lean::string_append(x_9, x_1);
x_11 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::string_append(x_12, x_2);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean::string_append(x_13, x_14);
lean::inc(x_5);
x_16 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_15, x_5, x_7);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_19 = l_Lean_Parser_builtinTermParsingTable;
x_20 = l_Lean_Parser_runBuiltinParserUnsafe(x_18, x_19, x_3, x_5, x_16);
return x_20;
}
else
{
lean::dec(x_17);
lean::dec(x_5);
lean::dec(x_3);
return x_16;
}
}
else
{
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_3);
return x_7;
}
}
}
obj* l_Lean_Parser_Term_unicodeInfixR(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_String_trim(x_1);
x_6 = l_String_trim(x_2);
lean::inc(x_6);
lean::inc(x_5);
x_7 = l_Lean_Parser_unicodeSymbolInfo(x_5, x_6, x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_10 = l_Lean_Parser_Parser_inhabited___closed__1;
x_11 = l_Lean_Parser_andthenInfo(x_7, x_10);
x_12 = l_Lean_Parser_epsilonInfo;
x_13 = l_Lean_Parser_andthenInfo(x_12, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_unicodeInfixR___elambda__1___boxed), 6, 3);
lean::closure_set(x_14, 0, x_5);
lean::closure_set(x_14, 1, x_6);
lean::closure_set(x_14, 2, x_9);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_Lean_Parser_Term_unicodeInfixR___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Term_unicodeInfixR___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
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
obj* l_Lean_Parser_Term_infixR___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_5);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_3);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_7);
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_1);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_1, x_11, x_4, x_6);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_2, x_4, x_12);
return x_16;
}
else
{
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_2);
return x_12;
}
}
else
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
}
obj* l_Lean_Parser_Term_infixR(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::inc(x_2);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_String_trim(x_1);
lean::inc(x_4);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_8 = l_Lean_Parser_Parser_inhabited___closed__1;
x_9 = l_Lean_Parser_andthenInfo(x_5, x_8);
x_10 = l_Lean_Parser_epsilonInfo;
x_11 = l_Lean_Parser_andthenInfo(x_10, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_infixR___elambda__1___boxed), 5, 2);
lean::closure_set(x_12, 0, x_4);
lean::closure_set(x_12, 1, x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_Term_infixR___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_infixR___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
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
obj* l_Lean_Parser_Term_unicodeInfixL___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_6);
x_7 = l_Lean_Parser_ParserState_pushSyntax(x_6, x_4);
x_8 = lean::cnstr_get(x_6, 3);
lean::inc(x_8);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_9 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_10 = lean::string_append(x_9, x_2);
x_11 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::string_append(x_12, x_3);
x_14 = l_Char_HasRepr___closed__1;
x_15 = lean::string_append(x_13, x_14);
lean::inc(x_5);
x_16 = l_Lean_Parser_unicodeSymbolFnAux(x_2, x_3, x_15, x_5, x_7);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_19 = l_Lean_Parser_builtinTermParsingTable;
x_20 = l_Lean_Parser_runBuiltinParserUnsafe(x_18, x_19, x_1, x_5, x_16);
return x_20;
}
else
{
lean::dec(x_17);
lean::dec(x_5);
lean::dec(x_1);
return x_16;
}
}
else
{
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_1);
return x_7;
}
}
}
obj* l_Lean_Parser_Term_unicodeInfixL(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_String_trim(x_1);
x_6 = l_String_trim(x_2);
lean::inc(x_6);
lean::inc(x_5);
x_7 = l_Lean_Parser_unicodeSymbolInfo(x_5, x_6, x_4);
x_8 = l_Lean_Parser_Parser_inhabited___closed__1;
x_9 = l_Lean_Parser_andthenInfo(x_7, x_8);
x_10 = l_Lean_Parser_epsilonInfo;
x_11 = l_Lean_Parser_andthenInfo(x_10, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_unicodeInfixL___elambda__1___boxed), 6, 3);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_6);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_Term_unicodeInfixL___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Term_unicodeInfixL___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
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
obj* l_Lean_Parser_Term_infixL___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_5);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_3);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_7);
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_9 = lean::string_append(x_8, x_2);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_9, x_10);
lean::inc(x_4);
x_12 = l_Lean_Parser_symbolFnAux(x_2, x_11, x_4, x_6);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_15 = l_Lean_Parser_builtinTermParsingTable;
x_16 = l_Lean_Parser_runBuiltinParserUnsafe(x_14, x_15, x_1, x_4, x_12);
return x_16;
}
else
{
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_1);
return x_12;
}
}
else
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
}
}
obj* l_Lean_Parser_Term_infixL(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_2);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = l_String_trim(x_1);
lean::inc(x_4);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_3);
x_6 = l_Lean_Parser_Parser_inhabited___closed__1;
x_7 = l_Lean_Parser_andthenInfo(x_5, x_6);
x_8 = l_Lean_Parser_epsilonInfo;
x_9 = l_Lean_Parser_andthenInfo(x_8, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_infixL___elambda__1___boxed), 5, 2);
lean::closure_set(x_10, 0, x_2);
lean::closure_set(x_10, 1, x_4);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_infixL___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Term_infixL___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
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
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, uint8 x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = l_Lean_Parser_levelParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinLevelParsingTable;
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_20 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_21 = lean::string_append(x_20, x_1);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_21, x_22);
lean::inc(x_7);
x_24 = l_Lean_Parser_symbolFnAux(x_1, x_23, x_7, x_15);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_19);
lean::dec(x_18);
{
uint8 _tmp_4 = x_3;
obj* _tmp_7 = x_24;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_25);
lean::dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_18, x_19);
lean::dec(x_18);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_4);
return x_29;
}
}
else
{
lean::dec(x_16);
lean::dec(x_7);
if (x_5 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_11);
lean::dec(x_10);
x_30 = lean::box(0);
x_31 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_30);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_4);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_Lean_Parser_ParserState_restore(x_15, x_10, x_11);
lean::dec(x_10);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_4);
return x_36;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___elambda__1___spec__1(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = 0;
x_10 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2(x_1, x_2, x_3, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_id___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(".{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_id___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(".{");
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
obj* _init_l_Lean_Parser_Term_id___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(", ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_id___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("}");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_id___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("}");
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
obj* _init_l_Lean_Parser_Term_id___elambda__1___closed__6() {
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
obj* l_Lean_Parser_Term_id___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_2);
x_6 = l_Lean_Parser_identFn___rarg(x_2, x_3);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_Term_id___elambda__1___closed__1;
x_12 = l_Lean_Parser_Term_id___elambda__1___closed__2;
lean::inc(x_2);
x_13 = l_Lean_Parser_symbolFnAux(x_11, x_12, x_2, x_6);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; uint8 x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_15 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_16 = 0;
x_17 = 0;
lean::inc(x_2);
x_18 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___elambda__1___spec__1(x_15, x_16, x_17, x_1, x_2, x_13);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_21 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_22 = l_Lean_Parser_symbolFnAux(x_20, x_21, x_2, x_18);
x_23 = lean::cnstr_get(x_22, 3);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
x_24 = l_Lean_nullKind;
x_25 = l_Lean_Parser_ParserState_mkNode(x_22, x_24, x_9);
x_26 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_5);
return x_27;
}
else
{
obj* x_28; uint8 x_29; 
lean::dec(x_23);
x_28 = lean::cnstr_get(x_22, 1);
lean::inc(x_28);
x_29 = lean::nat_dec_eq(x_28, x_10);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_10);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_22, x_30, x_9);
x_32 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_5);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = l_Lean_Parser_ParserState_restore(x_22, x_9, x_10);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_9);
x_37 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_5);
return x_38;
}
}
}
else
{
obj* x_39; uint8 x_40; 
lean::dec(x_19);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_18, 1);
lean::inc(x_39);
x_40 = lean::nat_dec_eq(x_39, x_10);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_10);
x_41 = l_Lean_nullKind;
x_42 = l_Lean_Parser_ParserState_mkNode(x_18, x_41, x_9);
x_43 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_44 = l_Lean_Parser_ParserState_mkNode(x_42, x_43, x_5);
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = l_Lean_Parser_ParserState_restore(x_18, x_9, x_10);
x_46 = l_Lean_nullKind;
x_47 = l_Lean_Parser_ParserState_mkNode(x_45, x_46, x_9);
x_48 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_49 = l_Lean_Parser_ParserState_mkNode(x_47, x_48, x_5);
return x_49;
}
}
}
else
{
obj* x_50; uint8 x_51; 
lean::dec(x_14);
lean::dec(x_2);
x_50 = lean::cnstr_get(x_13, 1);
lean::inc(x_50);
x_51 = lean::nat_dec_eq(x_50, x_10);
lean::dec(x_50);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_10);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_13, x_52, x_9);
x_54 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_55 = l_Lean_Parser_ParserState_mkNode(x_53, x_54, x_5);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = l_Lean_Parser_ParserState_restore(x_13, x_9, x_10);
x_57 = l_Lean_nullKind;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_9);
x_59 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_60 = l_Lean_Parser_ParserState_mkNode(x_58, x_59, x_5);
return x_60;
}
}
}
else
{
obj* x_61; obj* x_62; 
lean::dec(x_7);
lean::dec(x_2);
x_61 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_62 = l_Lean_Parser_ParserState_mkNode(x_6, x_61, x_5);
return x_62;
}
}
}
obj* _init_l_Lean_Parser_Term_id() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".{");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_symbolInfo(x_5, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_8 = lean::box(1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::mk_string(", ");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_symbolInfo(x_11, x_3);
x_13 = l_Lean_Parser_sepBy1Info(x_9, x_12);
x_14 = lean::mk_string("}");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
x_16 = l_Lean_Parser_symbolInfo(x_15, x_3);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_andthenInfo(x_6, x_17);
x_19 = l_Lean_Parser_noFirstTokenInfo(x_18);
x_20 = l_Lean_Parser_andthenInfo(x_2, x_19);
x_21 = l_Lean_Parser_nodeInfo(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_id___elambda__1___boxed), 3, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; uint8 x_10; uint8 x_11; obj* x_12; 
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_3);
lean::dec(x_3);
x_11 = lean::unbox(x_5);
lean::dec(x_5);
x_12 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2(x_1, x_9, x_10, x_4, x_11, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_1);
return x_12;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = lean::unbox(x_3);
lean::dec(x_3);
x_9 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_id___elambda__1___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Term_id___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_id___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_id(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_id___elambda__1___closed__6;
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
obj* _init_l_Lean_Parser_Term_type___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("Type");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_type___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("Type");
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
obj* _init_l_Lean_Parser_Term_type___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_type___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Term_type___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_type___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_type() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("Type");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_type___elambda__1___boxed), 1, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Term_type___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_type___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_type(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_type;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sort___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("Sort");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("Sort");
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
obj* _init_l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_sort___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Term_sort___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sort___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_sort() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("Sort");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sort___elambda__1___boxed), 1, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Term_sort___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_sort___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sort(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_sort;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1() {
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
obj* l_Lean_Parser_Term_hole___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Term_hole___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_hole___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_hole() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("_");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_hole___elambda__1___boxed), 1, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Term_hole___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_hole___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_hole(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_4 = l_Lean_Parser_Term_hole;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("sorry");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("sorry");
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
obj* _init_l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_sorry___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Term_sorry___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sorry___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_sorry() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("sorry");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sorry___elambda__1___boxed), 1, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Term_sorry___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_sorry___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sorry(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_sorry;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("·");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("·");
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
obj* _init_l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_cdot___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__2;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Term_cdot___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_cdot___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_cdot() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("·");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_cdot___elambda__1___boxed), 1, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Term_cdot___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_cdot___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_cdot(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_cdot;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" : ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" : ");
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
obj* _init_l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3() {
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
x_8 = lean::mk_string("typeAscription");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_typeAscription___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_typeAscription___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeAscription___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_typeAscription() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeAscription___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_typeAscription___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_typeAscription___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__2(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, uint8 x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinTermParsingTable;
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_20 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_21 = lean::string_append(x_20, x_1);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_21, x_22);
lean::inc(x_7);
x_24 = l_Lean_Parser_symbolFnAux(x_1, x_23, x_7, x_15);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_19);
lean::dec(x_18);
{
uint8 _tmp_4 = x_3;
obj* _tmp_7 = x_24;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_25);
lean::dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_18, x_19);
lean::dec(x_18);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_4);
return x_29;
}
}
else
{
lean::dec(x_16);
lean::dec(x_7);
if (x_5 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_11);
lean::dec(x_10);
x_30 = lean::box(0);
x_31 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_30);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_4);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_Lean_Parser_ParserState_restore(x_15, x_10, x_11);
lean::dec(x_10);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_4);
return x_36;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = 0;
x_10 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__2(x_1, x_2, x_3, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_tupleTail___elambda__1___closed__1() {
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
obj* _init_l_Lean_Parser_Term_tupleTail___elambda__1___closed__2() {
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
x_8 = lean::mk_string("tupleTail");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_tupleTail___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_7 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__1;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = 0;
x_11 = 0;
x_12 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(x_6, x_10, x_11, x_1, x_2, x_8);
x_13 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_5);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_9);
lean::dec(x_2);
x_15 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_8, x_15, x_5);
return x_16;
}
}
}
obj* _init_l_Lean_Parser_Term_tupleTail() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::box(0);
x_2 = lean::mk_string(", ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::inc(x_4);
x_8 = l_Lean_Parser_sepBy1Info(x_7, x_4);
x_9 = l_Lean_Parser_andthenInfo(x_4, x_8);
x_10 = l_Lean_Parser_nodeInfo(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_tupleTail___elambda__1___boxed), 3, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; uint8 x_10; uint8 x_11; obj* x_12; 
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_3);
lean::dec(x_3);
x_11 = lean::unbox(x_5);
lean::dec(x_5);
x_12 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__2(x_1, x_9, x_10, x_4, x_11, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_1);
return x_12;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = lean::unbox(x_3);
lean::dec(x_3);
x_9 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Term_tupleTail___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_tupleTail___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Term_parenSpecial___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
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
x_7 = l_Lean_Parser_Term_tupleTail___elambda__1(x_1, x_2, x_3);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_6);
lean::dec(x_2);
x_9 = l_Lean_nullKind;
x_10 = l_Lean_Parser_ParserState_mkNode(x_7, x_9, x_5);
return x_10;
}
else
{
obj* x_11; uint8 x_12; 
lean::dec(x_8);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
x_12 = lean::nat_dec_eq(x_11, x_6);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_6);
lean::dec(x_2);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_7, x_13, x_5);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_6);
x_15 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
x_16 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg(x_2, x_15);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_6);
x_18 = l_Lean_nullKind;
x_19 = l_Lean_Parser_ParserState_mkNode(x_16, x_18, x_5);
return x_19;
}
else
{
obj* x_20; uint8 x_21; 
lean::dec(x_17);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
x_21 = lean::nat_dec_eq(x_20, x_6);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_6);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_16, x_22, x_5);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_Lean_Parser_ParserState_restore(x_16, x_5, x_6);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_5);
return x_26;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Term_parenSpecial() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_Term_tupleTail;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Term_typeAscription;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
x_6 = l_Lean_Parser_noFirstTokenInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_parenSpecial___elambda__1___boxed), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Term_parenSpecial___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_parenSpecial___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_Term_paren___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_paren___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_7 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
x_49 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_50 = l_Lean_Parser_builtinTermParsingTable;
x_51 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_52 = l_Lean_Parser_runBuiltinParserUnsafe(x_49, x_50, x_51, x_2, x_8);
x_53 = lean::cnstr_get(x_52, 3);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; 
lean::inc(x_2);
x_54 = l_Lean_Parser_Term_parenSpecial___elambda__1(x_1, x_2, x_52);
x_13 = x_54;
goto block_48;
}
else
{
lean::dec(x_53);
x_13 = x_52;
goto block_48;
}
block_48:
{
obj* x_14; 
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_12);
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Parser_ParserState_mkNode(x_13, x_15, x_11);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_19 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_20 = l_Lean_Parser_symbolFnAux(x_18, x_19, x_2, x_16);
x_21 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_5);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_17);
lean::dec(x_2);
x_23 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_24 = l_Lean_Parser_ParserState_mkNode(x_16, x_23, x_5);
return x_24;
}
}
else
{
obj* x_25; uint8 x_26; 
lean::dec(x_14);
x_25 = lean::cnstr_get(x_13, 1);
lean::inc(x_25);
x_26 = lean::nat_dec_eq(x_25, x_12);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_12);
x_27 = l_Lean_nullKind;
x_28 = l_Lean_Parser_ParserState_mkNode(x_13, x_27, x_11);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_30 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_31 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_32 = l_Lean_Parser_symbolFnAux(x_30, x_31, x_2, x_28);
x_33 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_34 = l_Lean_Parser_ParserState_mkNode(x_32, x_33, x_5);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_29);
lean::dec(x_2);
x_35 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_36 = l_Lean_Parser_ParserState_mkNode(x_28, x_35, x_5);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
x_38 = l_Lean_nullKind;
x_39 = l_Lean_Parser_ParserState_mkNode(x_37, x_38, x_11);
x_40 = lean::cnstr_get(x_39, 3);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_41 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_42 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_43 = l_Lean_Parser_symbolFnAux(x_41, x_42, x_2, x_39);
x_44 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_45 = l_Lean_Parser_ParserState_mkNode(x_43, x_44, x_5);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_40);
lean::dec(x_2);
x_46 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_47 = l_Lean_Parser_ParserState_mkNode(x_39, x_46, x_5);
return x_47;
}
}
}
}
}
else
{
obj* x_55; obj* x_56; 
lean::dec(x_9);
lean::dec(x_2);
x_55 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_56 = l_Lean_Parser_ParserState_mkNode(x_8, x_55, x_5);
return x_56;
}
}
}
obj* _init_l_Lean_Parser_Term_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("(");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_Term_parenSpecial;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = l_Lean_Parser_andthenInfo(x_8, x_10);
x_12 = l_Lean_Parser_noFirstTokenInfo(x_11);
x_13 = lean::box(0);
x_14 = lean::mk_string(")");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
x_16 = l_Lean_Parser_symbolInfo(x_15, x_13);
x_17 = l_Lean_Parser_andthenInfo(x_12, x_16);
x_18 = l_Lean_Parser_andthenInfo(x_5, x_17);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_paren___elambda__1___boxed), 3, 0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l_Lean_Parser_Term_paren___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_paren___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_paren(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_paren;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("⟨");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("⟨");
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
obj* _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("⟩");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("⟩");
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
obj* _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5() {
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
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_11 = 0;
x_12 = 0;
lean::inc(x_2);
x_13 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(x_10, x_11, x_12, x_1, x_2, x_8);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__3;
x_16 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__4;
x_17 = l_Lean_Parser_symbolFnAux(x_15, x_16, x_2, x_13);
x_18 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_14);
lean::dec(x_2);
x_20 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5;
x_21 = l_Lean_Parser_ParserState_mkNode(x_13, x_20, x_5);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_2);
x_22 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5;
x_23 = l_Lean_Parser_ParserState_mkNode(x_8, x_22, x_5);
return x_23;
}
}
}
obj* _init_l_Lean_Parser_Term_anonymousCtor() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("⟨");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::box(0);
x_10 = lean::mk_string(", ");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_symbolInfo(x_11, x_9);
x_13 = l_Lean_Parser_sepBy1Info(x_8, x_12);
x_14 = lean::mk_string("⟩");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
x_16 = l_Lean_Parser_symbolInfo(x_15, x_9);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_andthenInfo(x_5, x_17);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_anonymousCtor___elambda__1___boxed), 3, 0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l_Lean_Parser_Term_anonymousCtor___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_anonymousCtor___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5;
x_4 = l_Lean_Parser_Term_anonymousCtor;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_Term_optIdent___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::array_get_size(x_3);
lean::dec(x_3);
lean::inc(x_1);
x_6 = l_Lean_Parser_identFn___rarg(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1;
x_9 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2;
x_10 = l_Lean_Parser_symbolFnAux(x_8, x_9, x_1, x_6);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_4);
x_12 = l_Lean_nullKind;
x_13 = l_Lean_Parser_ParserState_mkNode(x_10, x_12, x_5);
return x_13;
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_10);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_15 = lean::cnstr_get(x_10, 0);
x_16 = lean::cnstr_get(x_10, 3);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_10, 1);
lean::dec(x_17);
x_18 = l_Array_shrink___main___rarg(x_15, x_5);
lean::inc(x_4);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 0, x_18);
x_19 = lean::nat_dec_eq(x_4, x_4);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_4);
x_20 = l_Lean_nullKind;
x_21 = l_Lean_Parser_ParserState_mkNode(x_10, x_20, x_5);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_Lean_Parser_ParserState_restore(x_10, x_5, x_4);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_5);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_25 = lean::cnstr_get(x_10, 0);
x_26 = lean::cnstr_get(x_10, 2);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_10);
x_27 = l_Array_shrink___main___rarg(x_25, x_5);
lean::inc(x_4);
x_28 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_4);
lean::cnstr_set(x_28, 2, x_26);
lean::cnstr_set(x_28, 3, x_11);
x_29 = lean::nat_dec_eq(x_4, x_4);
if (x_29 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_4);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_28, x_30, x_5);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = l_Lean_Parser_ParserState_restore(x_28, x_5, x_4);
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_32, x_33, x_5);
return x_34;
}
}
}
}
else
{
obj* x_35; 
lean::dec(x_7);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_6, 3);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_37; 
lean::dec(x_4);
x_36 = l_Lean_nullKind;
x_37 = l_Lean_Parser_ParserState_mkNode(x_6, x_36, x_5);
return x_37;
}
else
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_6);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; uint8 x_43; 
x_39 = lean::cnstr_get(x_6, 0);
x_40 = lean::cnstr_get(x_6, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_6, 1);
lean::dec(x_41);
x_42 = l_Array_shrink___main___rarg(x_39, x_5);
lean::inc(x_4);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 0, x_42);
x_43 = lean::nat_dec_eq(x_4, x_4);
if (x_43 == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_4);
x_44 = l_Lean_nullKind;
x_45 = l_Lean_Parser_ParserState_mkNode(x_6, x_44, x_5);
return x_45;
}
else
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = l_Lean_Parser_ParserState_restore(x_6, x_5, x_4);
x_47 = l_Lean_nullKind;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_5);
return x_48;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; 
x_49 = lean::cnstr_get(x_6, 0);
x_50 = lean::cnstr_get(x_6, 2);
lean::inc(x_50);
lean::inc(x_49);
lean::dec(x_6);
x_51 = l_Array_shrink___main___rarg(x_49, x_5);
lean::inc(x_4);
x_52 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_4);
lean::cnstr_set(x_52, 2, x_50);
lean::cnstr_set(x_52, 3, x_35);
x_53 = lean::nat_dec_eq(x_4, x_4);
if (x_53 == 0)
{
obj* x_54; obj* x_55; 
lean::dec(x_4);
x_54 = l_Lean_nullKind;
x_55 = l_Lean_Parser_ParserState_mkNode(x_52, x_54, x_5);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_Lean_Parser_ParserState_restore(x_52, x_5, x_4);
x_57 = l_Lean_nullKind;
x_58 = l_Lean_Parser_ParserState_mkNode(x_56, x_57, x_5);
return x_58;
}
}
}
}
}
}
obj* l_Lean_Parser_Term_optIdent___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optIdent___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_optIdent() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(" : ");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_symbolInfo(x_5, x_3);
x_7 = l_Lean_Parser_andthenInfo(x_2, x_6);
x_8 = l_Lean_Parser_noFirstTokenInfo(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optIdent___elambda__1___boxed), 1, 0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_Term_optIdent___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_optIdent___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("if ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("if ");
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
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" then ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" then ");
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
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" else ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" else ");
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
obj* _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__7() {
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
obj* l_Lean_Parser_Term_if___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::inc(x_1);
x_9 = l_Lean_Parser_Term_optIdent___elambda__1___rarg(x_1, x_7);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_9);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__3;
x_17 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__4;
lean::inc(x_1);
x_18 = l_Lean_Parser_symbolFnAux(x_16, x_17, x_1, x_14);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
lean::inc(x_1);
x_20 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_18);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__5;
x_23 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__6;
lean::inc(x_1);
x_24 = l_Lean_Parser_symbolFnAux(x_22, x_23, x_1, x_20);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_24);
x_27 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_4);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_25);
lean::dec(x_1);
x_29 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_30 = l_Lean_Parser_ParserState_mkNode(x_24, x_29, x_4);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_21);
lean::dec(x_1);
x_31 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_32 = l_Lean_Parser_ParserState_mkNode(x_20, x_31, x_4);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_19);
lean::dec(x_1);
x_33 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_34 = l_Lean_Parser_ParserState_mkNode(x_18, x_33, x_4);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_15);
lean::dec(x_1);
x_35 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_36 = l_Lean_Parser_ParserState_mkNode(x_14, x_35, x_4);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_10);
lean::dec(x_1);
x_37 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_38 = l_Lean_Parser_ParserState_mkNode(x_9, x_37, x_4);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_8);
lean::dec(x_1);
x_39 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_40 = l_Lean_Parser_ParserState_mkNode(x_7, x_39, x_4);
return x_40;
}
}
}
obj* l_Lean_Parser_Term_if___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_if___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_if() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("if ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string(" then ");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolInfo(x_9, x_1);
x_11 = lean::mk_string(" else ");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
x_13 = l_Lean_Parser_symbolInfo(x_12, x_1);
lean::inc(x_7);
x_14 = l_Lean_Parser_andthenInfo(x_13, x_7);
lean::inc(x_7);
x_15 = l_Lean_Parser_andthenInfo(x_7, x_14);
x_16 = l_Lean_Parser_andthenInfo(x_10, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_7, x_16);
x_18 = l_Lean_Parser_Term_optIdent;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = l_Lean_Parser_andthenInfo(x_19, x_17);
x_21 = l_Lean_Parser_andthenInfo(x_4, x_20);
x_22 = l_Lean_Parser_nodeInfo(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_if___elambda__1___boxed), 1, 0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* l_Lean_Parser_Term_if___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_if___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_if(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_if___elambda__1___rarg___closed__7;
x_4 = l_Lean_Parser_Term_if;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" from ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" from ");
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
obj* _init_l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3() {
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
x_8 = lean::mk_string("fromTerm");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_fromTerm___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_fromTerm___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fromTerm___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_fromTerm() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" from ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fromTerm___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_fromTerm___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_fromTerm___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" := ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" := ");
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
obj* _init_l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3() {
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
x_8 = lean::mk_string("haveAssign");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_haveAssign___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_haveAssign___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_haveAssign() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" := ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_haveAssign___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_haveAssign___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_haveAssign___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("have ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("have ");
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
obj* _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("; ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("; ");
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
obj* _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__5() {
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
obj* l_Lean_Parser_Term_have___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::inc(x_1);
x_9 = l_Lean_Parser_Term_optIdent___elambda__1___rarg(x_1, x_7);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_9);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
lean::inc(x_1);
x_19 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg(x_1, x_14);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_18);
lean::dec(x_17);
x_21 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__3;
x_22 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__4;
lean::inc(x_1);
x_23 = l_Lean_Parser_symbolFnAux(x_21, x_22, x_1, x_19);
x_24 = lean::cnstr_get(x_23, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_23);
x_26 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_4);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_24);
lean::dec(x_1);
x_28 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_29 = l_Lean_Parser_ParserState_mkNode(x_23, x_28, x_4);
return x_29;
}
}
else
{
obj* x_30; uint8 x_31; 
lean::dec(x_20);
x_30 = lean::cnstr_get(x_19, 1);
lean::inc(x_30);
x_31 = lean::nat_dec_eq(x_30, x_18);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_18);
lean::dec(x_17);
lean::dec(x_1);
x_32 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_33 = l_Lean_Parser_ParserState_mkNode(x_19, x_32, x_4);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_Lean_Parser_ParserState_restore(x_19, x_17, x_18);
lean::dec(x_17);
lean::inc(x_1);
x_35 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg(x_1, x_34);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__3;
x_38 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__4;
lean::inc(x_1);
x_39 = l_Lean_Parser_symbolFnAux(x_37, x_38, x_1, x_35);
x_40 = lean::cnstr_get(x_39, 3);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_39);
x_42 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_43 = l_Lean_Parser_ParserState_mkNode(x_41, x_42, x_4);
return x_43;
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_40);
lean::dec(x_1);
x_44 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_45 = l_Lean_Parser_ParserState_mkNode(x_39, x_44, x_4);
return x_45;
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_36);
lean::dec(x_1);
x_46 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_47 = l_Lean_Parser_ParserState_mkNode(x_35, x_46, x_4);
return x_47;
}
}
}
}
else
{
obj* x_48; obj* x_49; 
lean::dec(x_15);
lean::dec(x_1);
x_48 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_49 = l_Lean_Parser_ParserState_mkNode(x_14, x_48, x_4);
return x_49;
}
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_10);
lean::dec(x_1);
x_50 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_51 = l_Lean_Parser_ParserState_mkNode(x_9, x_50, x_4);
return x_51;
}
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_8);
lean::dec(x_1);
x_52 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_53 = l_Lean_Parser_ParserState_mkNode(x_7, x_52, x_4);
return x_53;
}
}
}
obj* l_Lean_Parser_Term_have___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_have___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_have() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_1 = lean::box(0);
x_2 = lean::mk_string("have ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_Term_haveAssign;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_Term_fromTerm;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = l_Lean_Parser_orelseInfo(x_9, x_11);
x_13 = lean::mk_string("; ");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
x_15 = l_Lean_Parser_symbolInfo(x_14, x_1);
lean::inc(x_7);
x_16 = l_Lean_Parser_andthenInfo(x_15, x_7);
x_17 = l_Lean_Parser_andthenInfo(x_12, x_16);
x_18 = l_Lean_Parser_andthenInfo(x_7, x_17);
x_19 = l_Lean_Parser_Term_optIdent;
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_21 = l_Lean_Parser_andthenInfo(x_20, x_18);
x_22 = l_Lean_Parser_andthenInfo(x_4, x_21);
x_23 = l_Lean_Parser_nodeInfo(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_have___elambda__1___boxed), 1, 0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* l_Lean_Parser_Term_have___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_have___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_have(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__5;
x_4 = l_Lean_Parser_Term_have;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("suffices ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("suffices ");
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
obj* _init_l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_suffices___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::inc(x_1);
x_9 = l_Lean_Parser_Term_optIdent___elambda__1___rarg(x_1, x_7);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_9);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; 
lean::inc(x_1);
x_16 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg(x_1, x_14);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__3;
x_19 = l_Lean_Parser_Term_have___elambda__1___rarg___closed__4;
lean::inc(x_1);
x_20 = l_Lean_Parser_symbolFnAux(x_18, x_19, x_1, x_16);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_20);
x_23 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_4);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_21);
lean::dec(x_1);
x_25 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_26 = l_Lean_Parser_ParserState_mkNode(x_20, x_25, x_4);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_17);
lean::dec(x_1);
x_27 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_28 = l_Lean_Parser_ParserState_mkNode(x_16, x_27, x_4);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_15);
lean::dec(x_1);
x_29 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_30 = l_Lean_Parser_ParserState_mkNode(x_14, x_29, x_4);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_10);
lean::dec(x_1);
x_31 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_32 = l_Lean_Parser_ParserState_mkNode(x_9, x_31, x_4);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_8);
lean::dec(x_1);
x_33 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_34 = l_Lean_Parser_ParserState_mkNode(x_7, x_33, x_4);
return x_34;
}
}
}
obj* l_Lean_Parser_Term_suffices___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_suffices___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_suffices() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::box(0);
x_2 = lean::mk_string("suffices ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("; ");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolInfo(x_9, x_1);
lean::inc(x_7);
x_11 = l_Lean_Parser_andthenInfo(x_10, x_7);
x_12 = l_Lean_Parser_Term_fromTerm;
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_andthenInfo(x_13, x_11);
x_15 = l_Lean_Parser_andthenInfo(x_7, x_14);
x_16 = l_Lean_Parser_Term_optIdent;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = l_Lean_Parser_andthenInfo(x_17, x_15);
x_19 = l_Lean_Parser_andthenInfo(x_4, x_18);
x_20 = l_Lean_Parser_nodeInfo(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_suffices___elambda__1___boxed), 1, 0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
obj* l_Lean_Parser_Term_suffices___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_suffices___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_suffices(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_suffices;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_show___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("show ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_show___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("show ");
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
obj* _init_l_Lean_Parser_Term_show___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_show___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_show___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_show___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_Parser_Term_fromTerm___elambda__1___rarg(x_1, x_12);
x_15 = l_Lean_Parser_Term_show___elambda__1___rarg___closed__3;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::dec(x_1);
x_17 = l_Lean_Parser_Term_show___elambda__1___rarg___closed__3;
x_18 = l_Lean_Parser_ParserState_mkNode(x_12, x_17, x_4);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_8);
lean::dec(x_1);
x_19 = l_Lean_Parser_Term_show___elambda__1___rarg___closed__3;
x_20 = l_Lean_Parser_ParserState_mkNode(x_7, x_19, x_4);
return x_20;
}
}
}
obj* l_Lean_Parser_Term_show___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_show___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_show() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::box(0);
x_2 = lean::mk_string("show ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_Term_fromTerm;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_andthenInfo(x_7, x_9);
x_11 = l_Lean_Parser_andthenInfo(x_4, x_10);
x_12 = l_Lean_Parser_nodeInfo(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_show___elambda__1___boxed), 1, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_Lean_Parser_Term_show___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_show___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_show(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_show___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_show;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_fun___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_8 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_9 = l_Lean_Parser_builtinTermParsingTable;
x_10 = l_Lean_Parser_appPrec;
lean::inc(x_3);
x_11 = l_Lean_Parser_runBuiltinParserUnsafe(x_8, x_9, x_10, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
lean::dec(x_6);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_14 = lean::nat_dec_eq(x_7, x_13);
lean::dec(x_13);
lean::dec(x_7);
if (x_14 == 0)
{
x_4 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_3);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_11, x_16);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_3);
x_18 = l_Lean_Parser_ParserState_restore(x_11, x_6, x_7);
lean::dec(x_6);
return x_18;
}
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("λ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("fun");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string("λ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("fun");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = lean::mk_string("expected '");
x_6 = lean::string_append(x_5, x_2);
lean::dec(x_2);
x_7 = lean::mk_string("' or '");
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
x_9 = lean::string_append(x_8, x_4);
lean::dec(x_4);
x_10 = lean::mk_string("'");
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("⇒");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("=>");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string("⇒");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("=>");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = lean::mk_string("expected '");
x_6 = lean::string_append(x_5, x_2);
lean::dec(x_2);
x_7 = lean::mk_string("' or '");
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
x_9 = lean::string_append(x_8, x_4);
lean::dec(x_4);
x_10 = lean::mk_string("'");
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_fun___elambda__1___closed__7() {
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
obj* l_Lean_Parser_Term_fun___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_fun___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_8 = l_Lean_Parser_Term_fun___elambda__1___closed__3;
lean::inc(x_2);
x_9 = l_Lean_Parser_unicodeSymbolFnAux(x_6, x_7, x_8, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
x_13 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_14 = l_Lean_Parser_builtinTermParsingTable;
x_15 = l_Lean_Parser_appPrec;
lean::inc(x_2);
x_16 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_15, x_2, x_9);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = 0;
lean::inc(x_2);
x_19 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_fun___elambda__1___spec__1(x_18, x_1, x_2, x_16);
x_20 = l_Lean_nullKind;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_12);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = l_Lean_Parser_Term_fun___elambda__1___closed__4;
x_24 = l_Lean_Parser_Term_fun___elambda__1___closed__5;
x_25 = l_Lean_Parser_Term_fun___elambda__1___closed__6;
lean::inc(x_2);
x_26 = l_Lean_Parser_unicodeSymbolFnAux(x_23, x_24, x_25, x_2, x_21);
x_27 = lean::cnstr_get(x_26, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::mk_nat_obj(0u);
x_29 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_28, x_2, x_26);
x_30 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_5);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_27);
lean::dec(x_2);
x_32 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_33 = l_Lean_Parser_ParserState_mkNode(x_26, x_32, x_5);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
lean::dec(x_22);
lean::dec(x_2);
x_34 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_35 = l_Lean_Parser_ParserState_mkNode(x_21, x_34, x_5);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_17);
x_36 = l_Lean_nullKind;
x_37 = l_Lean_Parser_ParserState_mkNode(x_16, x_36, x_12);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_39 = l_Lean_Parser_Term_fun___elambda__1___closed__4;
x_40 = l_Lean_Parser_Term_fun___elambda__1___closed__5;
x_41 = l_Lean_Parser_Term_fun___elambda__1___closed__6;
lean::inc(x_2);
x_42 = l_Lean_Parser_unicodeSymbolFnAux(x_39, x_40, x_41, x_2, x_37);
x_43 = lean::cnstr_get(x_42, 3);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = lean::mk_nat_obj(0u);
x_45 = l_Lean_Parser_runBuiltinParserUnsafe(x_13, x_14, x_44, x_2, x_42);
x_46 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_47 = l_Lean_Parser_ParserState_mkNode(x_45, x_46, x_5);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
lean::dec(x_43);
lean::dec(x_2);
x_48 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_49 = l_Lean_Parser_ParserState_mkNode(x_42, x_48, x_5);
return x_49;
}
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_38);
lean::dec(x_2);
x_50 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_51 = l_Lean_Parser_ParserState_mkNode(x_37, x_50, x_5);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_10);
lean::dec(x_2);
x_52 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_53 = l_Lean_Parser_ParserState_mkNode(x_9, x_52, x_5);
return x_53;
}
}
}
obj* _init_l_Lean_Parser_Term_fun() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::box(0);
x_2 = lean::mk_string("λ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::mk_string("fun");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_unicodeSymbolInfo(x_3, x_5, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_8 = lean::box(1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::mk_string("⇒");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_12 = lean::mk_string("=>");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = l_Lean_Parser_unicodeSymbolInfo(x_11, x_13, x_1);
lean::inc(x_9);
x_15 = l_Lean_Parser_andthenInfo(x_14, x_9);
x_16 = l_Lean_Parser_andthenInfo(x_9, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_6, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fun___elambda__1___boxed), 3, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_fun___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_fun___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_fun___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_fun___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_fun(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_fun___elambda__1___closed__7;
x_4 = l_Lean_Parser_Term_fun;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1() {
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
x_8 = lean::mk_string("structInstField");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_structInstField___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
lean::inc(x_1);
x_5 = l_Lean_Parser_identFn___rarg(x_1, x_2);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1;
x_8 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_9 = l_Lean_Parser_symbolFnAux(x_7, x_8, x_1, x_5);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_9);
x_15 = l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_10);
lean::dec(x_1);
x_17 = l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1;
x_18 = l_Lean_Parser_ParserState_mkNode(x_9, x_17, x_4);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_1);
x_19 = l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1;
x_20 = l_Lean_Parser_ParserState_mkNode(x_5, x_19, x_4);
return x_20;
}
}
}
obj* l_Lean_Parser_Term_structInstField___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInstField___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_structInstField() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(" := ");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_symbolInfo(x_5, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_8 = lean::box(1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_andthenInfo(x_6, x_9);
x_11 = l_Lean_Parser_andthenInfo(x_2, x_10);
x_12 = l_Lean_Parser_nodeInfo(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInstField___elambda__1___boxed), 1, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_Lean_Parser_Term_structInstField___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_structInstField___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("..");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("..");
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
obj* _init_l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3() {
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
x_8 = lean::mk_string("structInstSource");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_structInstSource___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
x_12 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinTermParsingTable;
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_1, x_7);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_11);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_15, x_17, x_10);
x_19 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_4);
return x_20;
}
else
{
obj* x_21; uint8 x_22; 
lean::dec(x_16);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
x_22 = lean::nat_dec_eq(x_21, x_11);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_11);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_15, x_23, x_10);
x_25 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = l_Lean_Parser_ParserState_restore(x_15, x_10, x_11);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_10);
x_30 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3;
x_31 = l_Lean_Parser_ParserState_mkNode(x_29, x_30, x_4);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_8);
lean::dec(x_1);
x_32 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3;
x_33 = l_Lean_Parser_ParserState_mkNode(x_7, x_32, x_4);
return x_33;
}
}
}
obj* l_Lean_Parser_Term_structInstSource___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInstSource___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_structInstSource() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::box(0);
x_2 = lean::mk_string("..");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_noFirstTokenInfo(x_7);
x_9 = l_Lean_Parser_andthenInfo(x_4, x_8);
x_10 = l_Lean_Parser_nodeInfo(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInstSource___elambda__1___boxed), 1, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_Lean_Parser_Term_structInstSource___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_structInstSource___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___elambda__1___spec__2(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, uint8 x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_35; obj* x_36; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::inc(x_7);
x_35 = l_Lean_Parser_Term_structInstField___elambda__1___rarg(x_7, x_8);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
x_12 = x_35;
goto block_34;
}
else
{
obj* x_37; uint8 x_38; 
lean::dec(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
x_38 = lean::nat_dec_eq(x_37, x_11);
lean::dec(x_37);
if (x_38 == 0)
{
x_12 = x_35;
goto block_34;
}
else
{
obj* x_39; obj* x_40; 
lean::inc(x_11);
x_39 = l_Lean_Parser_ParserState_restore(x_35, x_10, x_11);
lean::inc(x_7);
x_40 = l_Lean_Parser_Term_structInstSource___elambda__1___rarg(x_7, x_39);
x_12 = x_40;
goto block_34;
}
}
block_34:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = lean::array_get_size(x_14);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
x_17 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_18 = lean::string_append(x_17, x_1);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean::string_append(x_18, x_19);
lean::inc(x_7);
x_21 = l_Lean_Parser_symbolFnAux(x_1, x_20, x_7, x_12);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_16);
lean::dec(x_15);
{
uint8 _tmp_4 = x_3;
obj* _tmp_7 = x_21;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
lean::dec(x_7);
x_24 = l_Lean_Parser_ParserState_restore(x_21, x_15, x_16);
lean::dec(x_15);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
}
}
else
{
lean::dec(x_13);
lean::dec(x_7);
if (x_5 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_11);
lean::dec(x_10);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_12, x_27);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_4);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_restore(x_12, x_10, x_11);
lean::dec(x_10);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_4);
return x_33;
}
}
}
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = 1;
x_10 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___elambda__1___spec__2(x_1, x_2, x_3, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_structInst___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_structInst___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("{");
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
obj* _init_l_Lean_Parser_Term_structInst___elambda__1___closed__3() {
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
obj* _init_l_Lean_Parser_Term_structInst___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" . ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_structInst___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" . ");
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
obj* l_Lean_Parser_Term_structInst___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_structInst___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_70; obj* x_71; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = lean::array_get_size(x_10);
lean::dec(x_10);
lean::inc(x_2);
x_70 = l_Lean_Parser_identFn___rarg(x_2, x_8);
x_71 = lean::cnstr_get(x_70, 3);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_72 = l_Lean_Parser_Term_structInst___elambda__1___closed__4;
x_73 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
lean::inc(x_2);
x_74 = l_Lean_Parser_symbolFnAux(x_72, x_73, x_2, x_70);
x_75 = lean::cnstr_get(x_74, 3);
lean::inc(x_75);
if (lean::obj_tag(x_75) == 0)
{
x_13 = x_74;
goto block_69;
}
else
{
uint8 x_76; 
x_76 = !lean::is_exclusive(x_74);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_74, 0);
x_78 = lean::cnstr_get(x_74, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_74, 1);
lean::dec(x_79);
x_80 = l_Array_shrink___main___rarg(x_77, x_12);
lean::inc(x_11);
lean::cnstr_set(x_74, 1, x_11);
lean::cnstr_set(x_74, 0, x_80);
x_13 = x_74;
goto block_69;
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_74, 0);
x_82 = lean::cnstr_get(x_74, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_74);
x_83 = l_Array_shrink___main___rarg(x_81, x_12);
lean::inc(x_11);
x_84 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_11);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_75);
x_13 = x_84;
goto block_69;
}
}
}
else
{
obj* x_85; 
lean::dec(x_71);
x_85 = lean::cnstr_get(x_70, 3);
lean::inc(x_85);
if (lean::obj_tag(x_85) == 0)
{
x_13 = x_70;
goto block_69;
}
else
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_70);
if (x_86 == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_87 = lean::cnstr_get(x_70, 0);
x_88 = lean::cnstr_get(x_70, 3);
lean::dec(x_88);
x_89 = lean::cnstr_get(x_70, 1);
lean::dec(x_89);
x_90 = l_Array_shrink___main___rarg(x_87, x_12);
lean::inc(x_11);
lean::cnstr_set(x_70, 1, x_11);
lean::cnstr_set(x_70, 0, x_90);
x_13 = x_70;
goto block_69;
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_70, 0);
x_92 = lean::cnstr_get(x_70, 2);
lean::inc(x_92);
lean::inc(x_91);
lean::dec(x_70);
x_93 = l_Array_shrink___main___rarg(x_91, x_12);
lean::inc(x_11);
x_94 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_11);
lean::cnstr_set(x_94, 2, x_92);
lean::cnstr_set(x_94, 3, x_85);
x_13 = x_94;
goto block_69;
}
}
}
block_69:
{
obj* x_14; 
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_11);
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Parser_ParserState_mkNode(x_13, x_15, x_12);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; uint8 x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_18 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_19 = 0;
x_20 = 1;
lean::inc(x_2);
x_21 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1(x_18, x_19, x_20, x_1, x_2, x_16);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_24 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_25 = l_Lean_Parser_symbolFnAux(x_23, x_24, x_2, x_21);
x_26 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_5);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_2);
x_28 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_29 = l_Lean_Parser_ParserState_mkNode(x_21, x_28, x_5);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_17);
lean::dec(x_2);
x_30 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_31 = l_Lean_Parser_ParserState_mkNode(x_16, x_30, x_5);
return x_31;
}
}
else
{
obj* x_32; uint8 x_33; 
lean::dec(x_14);
x_32 = lean::cnstr_get(x_13, 1);
lean::inc(x_32);
x_33 = lean::nat_dec_eq(x_32, x_11);
lean::dec(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
x_34 = l_Lean_nullKind;
x_35 = l_Lean_Parser_ParserState_mkNode(x_13, x_34, x_12);
x_36 = lean::cnstr_get(x_35, 3);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; uint8 x_38; uint8 x_39; obj* x_40; obj* x_41; 
x_37 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_38 = 0;
x_39 = 1;
lean::inc(x_2);
x_40 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1(x_37, x_38, x_39, x_1, x_2, x_35);
x_41 = lean::cnstr_get(x_40, 3);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_43 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_44 = l_Lean_Parser_symbolFnAux(x_42, x_43, x_2, x_40);
x_45 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_5);
return x_46;
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_41);
lean::dec(x_2);
x_47 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_48 = l_Lean_Parser_ParserState_mkNode(x_40, x_47, x_5);
return x_48;
}
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_36);
lean::dec(x_2);
x_49 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_50 = l_Lean_Parser_ParserState_mkNode(x_35, x_49, x_5);
return x_50;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_51 = l_Lean_Parser_ParserState_restore(x_13, x_12, x_11);
x_52 = l_Lean_nullKind;
x_53 = l_Lean_Parser_ParserState_mkNode(x_51, x_52, x_12);
x_54 = lean::cnstr_get(x_53, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; uint8 x_56; uint8 x_57; obj* x_58; obj* x_59; 
x_55 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_56 = 0;
x_57 = 1;
lean::inc(x_2);
x_58 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1(x_55, x_56, x_57, x_1, x_2, x_53);
x_59 = lean::cnstr_get(x_58, 3);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_61 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_62 = l_Lean_Parser_symbolFnAux(x_60, x_61, x_2, x_58);
x_63 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_64 = l_Lean_Parser_ParserState_mkNode(x_62, x_63, x_5);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_59);
lean::dec(x_2);
x_65 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_66 = l_Lean_Parser_ParserState_mkNode(x_58, x_65, x_5);
return x_66;
}
}
else
{
obj* x_67; obj* x_68; 
lean::dec(x_54);
lean::dec(x_2);
x_67 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_68 = l_Lean_Parser_ParserState_mkNode(x_53, x_67, x_5);
return x_68;
}
}
}
}
}
else
{
obj* x_95; obj* x_96; 
lean::dec(x_9);
lean::dec(x_2);
x_95 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_96 = l_Lean_Parser_ParserState_mkNode(x_8, x_95, x_5);
return x_96;
}
}
}
obj* _init_l_Lean_Parser_Term_structInst() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("{");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = lean::mk_string("ident");
x_7 = l_Lean_Parser_mkAtomicInfo(x_6);
x_8 = lean::box(0);
x_9 = lean::mk_string(" . ");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_symbolInfo(x_10, x_8);
x_12 = l_Lean_Parser_andthenInfo(x_7, x_11);
x_13 = l_Lean_Parser_noFirstTokenInfo(x_12);
x_14 = l_Lean_Parser_Term_structInstField;
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_16 = l_Lean_Parser_Term_structInstSource;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = l_Lean_Parser_orelseInfo(x_15, x_17);
x_19 = lean::mk_string(", ");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
x_21 = l_Lean_Parser_symbolInfo(x_20, x_8);
x_22 = l_Lean_Parser_sepByInfo(x_18, x_21);
x_23 = lean::mk_string("}");
x_24 = l_String_trim(x_23);
lean::dec(x_23);
x_25 = l_Lean_Parser_symbolInfo(x_24, x_8);
x_26 = l_Lean_Parser_andthenInfo(x_22, x_25);
x_27 = l_Lean_Parser_andthenInfo(x_13, x_26);
x_28 = l_Lean_Parser_andthenInfo(x_5, x_27);
x_29 = l_Lean_Parser_nodeInfo(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_structInst___elambda__1___boxed), 3, 0);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; uint8 x_10; uint8 x_11; obj* x_12; 
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_3);
lean::dec(x_3);
x_11 = lean::unbox(x_5);
lean::dec(x_5);
x_12 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_structInst___elambda__1___spec__2(x_1, x_9, x_10, x_4, x_11, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_1);
return x_12;
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = lean::unbox(x_3);
lean::dec(x_3);
x_9 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_structInst___elambda__1___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Term_structInst___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_structInst___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_structInst(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_structInst___elambda__1___closed__3;
x_4 = l_Lean_Parser_Term_structInst;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1() {
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
x_8 = lean::mk_string("typeSpec");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_typeSpec___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_typeSpec___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_typeSpec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_typeSpec___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_typeSpec___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Term_optType___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_Term_typeSpec___elambda__1___rarg(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_5);
x_8 = l_Lean_nullKind;
x_9 = l_Lean_Parser_ParserState_mkNode(x_6, x_8, x_4);
return x_9;
}
else
{
obj* x_10; uint8 x_11; 
lean::dec(x_7);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_11 = lean::nat_dec_eq(x_10, x_5);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_5);
x_12 = l_Lean_nullKind;
x_13 = l_Lean_Parser_ParserState_mkNode(x_6, x_12, x_4);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
return x_16;
}
}
}
}
obj* l_Lean_Parser_Term_optType___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optType___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_optType() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Term_typeSpec;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optType___elambda__1___boxed), 1, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Term_optType___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_optType___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" // ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" // ");
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
obj* _init_l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_subtype___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
x_6 = l_Lean_Parser_Term_structInst___elambda__1___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::inc(x_1);
x_9 = l_Lean_Parser_identFn___rarg(x_1, x_7);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_1);
x_11 = l_Lean_Parser_Term_optType___elambda__1___rarg(x_1, x_9);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__1;
x_14 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_15 = l_Lean_Parser_symbolFnAux(x_13, x_14, x_1, x_11);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_18 = l_Lean_Parser_builtinTermParsingTable;
x_19 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_20 = l_Lean_Parser_runBuiltinParserUnsafe(x_17, x_18, x_19, x_1, x_15);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_23 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_24 = l_Lean_Parser_symbolFnAux(x_22, x_23, x_1, x_20);
x_25 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_4);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_21);
lean::dec(x_1);
x_27 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_28 = l_Lean_Parser_ParserState_mkNode(x_20, x_27, x_4);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_16);
lean::dec(x_1);
x_29 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_30 = l_Lean_Parser_ParserState_mkNode(x_15, x_29, x_4);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_12);
lean::dec(x_1);
x_31 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_32 = l_Lean_Parser_ParserState_mkNode(x_11, x_31, x_4);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_10);
lean::dec(x_1);
x_33 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_34 = l_Lean_Parser_ParserState_mkNode(x_9, x_33, x_4);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_8);
lean::dec(x_1);
x_35 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_36 = l_Lean_Parser_ParserState_mkNode(x_7, x_35, x_4);
return x_36;
}
}
}
obj* l_Lean_Parser_Term_subtype___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_subtype___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_subtype() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_1 = lean::box(0);
x_2 = lean::mk_string("{");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::mk_string("ident");
x_6 = l_Lean_Parser_mkAtomicInfo(x_5);
x_7 = lean::mk_string(" // ");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_symbolInfo(x_8, x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_11 = lean::box(1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::mk_string("}");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
x_15 = l_Lean_Parser_symbolInfo(x_14, x_1);
x_16 = l_Lean_Parser_andthenInfo(x_12, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_9, x_16);
x_18 = l_Lean_Parser_Term_optType;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = l_Lean_Parser_andthenInfo(x_19, x_17);
x_21 = l_Lean_Parser_andthenInfo(x_6, x_20);
x_22 = l_Lean_Parser_andthenInfo(x_4, x_21);
x_23 = l_Lean_Parser_nodeInfo(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_subtype___elambda__1___boxed), 1, 0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* l_Lean_Parser_Term_subtype___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_subtype___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_subtype(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_subtype;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___elambda__1___spec__2(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, uint8 x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinTermParsingTable;
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_7, x_8);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::array_get_size(x_17);
lean::dec(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_20 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_21 = lean::string_append(x_20, x_1);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_21, x_22);
lean::inc(x_7);
x_24 = l_Lean_Parser_symbolFnAux(x_1, x_23, x_7, x_15);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_19);
lean::dec(x_18);
{
uint8 _tmp_4 = x_3;
obj* _tmp_7 = x_24;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_25);
lean::dec(x_7);
x_27 = l_Lean_Parser_ParserState_restore(x_24, x_18, x_19);
lean::dec(x_18);
x_28 = l_Lean_nullKind;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_4);
return x_29;
}
}
else
{
lean::dec(x_16);
lean::dec(x_7);
if (x_5 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_11);
lean::dec(x_10);
x_30 = lean::box(0);
x_31 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_30);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_4);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_Lean_Parser_ParserState_restore(x_15, x_10, x_11);
lean::dec(x_10);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_4);
return x_36;
}
}
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___elambda__1___spec__1(obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = 1;
x_10 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___elambda__1___spec__2(x_1, x_2, x_3, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
obj* _init_l_Lean_Parser_Term_list___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("[");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_list___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("[");
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
obj* _init_l_Lean_Parser_Term_list___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(",");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_list___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("]");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_list___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("]");
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
obj* _init_l_Lean_Parser_Term_list___elambda__1___closed__6() {
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
obj* l_Lean_Parser_Term_list___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_list___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_list___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = l_Lean_Parser_Term_list___elambda__1___closed__3;
x_11 = 0;
x_12 = 1;
lean::inc(x_2);
x_13 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___elambda__1___spec__1(x_10, x_11, x_12, x_1, x_2, x_8);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = l_Lean_Parser_Term_list___elambda__1___closed__4;
x_16 = l_Lean_Parser_Term_list___elambda__1___closed__5;
x_17 = l_Lean_Parser_symbolFnAux(x_15, x_16, x_2, x_13);
x_18 = l_Lean_Parser_Term_list___elambda__1___closed__6;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_14);
lean::dec(x_2);
x_20 = l_Lean_Parser_Term_list___elambda__1___closed__6;
x_21 = l_Lean_Parser_ParserState_mkNode(x_13, x_20, x_5);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_2);
x_22 = l_Lean_Parser_Term_list___elambda__1___closed__6;
x_23 = l_Lean_Parser_ParserState_mkNode(x_8, x_22, x_5);
return x_23;
}
}
}
obj* _init_l_Lean_Parser_Term_list() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::mk_string("[");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_7 = lean::box(1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::box(0);
x_10 = lean::mk_string(",");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_symbolInfo(x_11, x_9);
x_13 = l_Lean_Parser_sepByInfo(x_8, x_12);
x_14 = lean::mk_string("]");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
x_16 = l_Lean_Parser_symbolInfo(x_15, x_9);
x_17 = l_Lean_Parser_andthenInfo(x_13, x_16);
x_18 = l_Lean_Parser_andthenInfo(x_5, x_17);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_list___elambda__1___boxed), 3, 0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; uint8 x_10; uint8 x_11; obj* x_12; 
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_3);
lean::dec(x_3);
x_11 = lean::unbox(x_5);
lean::dec(x_5);
x_12 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_list___elambda__1___spec__2(x_1, x_9, x_10, x_4, x_11, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_1);
return x_12;
}
}
obj* l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = lean::unbox(x_3);
lean::dec(x_3);
x_9 = l_Lean_Parser_sepByFn___main___at_Lean_Parser_Term_list___elambda__1___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Term_list___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_list___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_list(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_list___elambda__1___closed__6;
x_4 = l_Lean_Parser_Term_list;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Parser_Term_binderIdent___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::inc(x_1);
x_6 = l_Lean_Parser_identFn___rarg(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_8; uint8 x_9; 
lean::dec(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::nat_dec_eq(x_8, x_5);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_10; obj* x_11; 
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean::dec(x_4);
x_11 = l_Lean_Parser_Term_hole___elambda__1___rarg(x_1, x_10);
return x_11;
}
}
}
}
obj* l_Lean_Parser_Term_binderIdent___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderIdent___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_binderIdent() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = l_Lean_Parser_Term_hole;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderIdent___elambda__1___boxed), 1, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_Term_binderIdent___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_binderIdent___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Term_binderType___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1;
x_7 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_11 = l_Lean_Parser_builtinTermParsingTable;
x_12 = lean::mk_nat_obj(0u);
x_13 = l_Lean_Parser_runBuiltinParserUnsafe(x_10, x_11, x_12, x_1, x_8);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_5);
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Parser_ParserState_mkNode(x_13, x_15, x_4);
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_14);
x_17 = lean::cnstr_get(x_13, 1);
lean::inc(x_17);
x_18 = lean::nat_dec_eq(x_17, x_5);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_5);
x_19 = l_Lean_nullKind;
x_20 = l_Lean_Parser_ParserState_mkNode(x_13, x_19, x_4);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = l_Lean_Parser_ParserState_restore(x_13, x_4, x_5);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_4);
return x_23;
}
}
}
else
{
obj* x_24; uint8 x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_8, 1);
lean::inc(x_24);
x_25 = lean::nat_dec_eq(x_24, x_5);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_5);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_8, x_26, x_4);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_Lean_Parser_ParserState_restore(x_8, x_4, x_5);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_4);
return x_30;
}
}
}
}
obj* l_Lean_Parser_Term_binderType___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderType___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_Term_binderType___elambda__2___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1;
x_4 = l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_5 = l_Lean_Parser_symbolFnAux(x_3, x_4, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_8 = l_Lean_Parser_builtinTermParsingTable;
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Lean_Parser_runBuiltinParserUnsafe(x_7, x_8, x_9, x_1, x_5);
return x_10;
}
else
{
lean::dec(x_6);
lean::dec(x_1);
return x_5;
}
}
}
obj* l_Lean_Parser_Term_binderType___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderType___elambda__2___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_binderType___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_noFirstTokenInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderType___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_binderType___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderType___elambda__2___boxed), 1, 0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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
obj* l_Lean_Parser_Term_binderType___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_binderType___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Term_binderType___elambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_binderType___elambda__2(x_1);
lean::dec(x_1);
return x_2;
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
obj* _init_l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1() {
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
x_8 = lean::mk_string("binderDefault");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_binderDefault___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_binderDefault___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_binderDefault() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" := ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_binderDefault___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_binderDefault___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1() {
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
x_8 = lean::mk_string("binderTactic");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_binderTactic___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_structInst___elambda__1___closed__4;
x_6 = l_Lean_Parser_Term_structInst___elambda__1___closed__5;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_binderTactic___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderTactic___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_binderTactic() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" . ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderTactic___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_binderTactic___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_binderTactic___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_8 = l_Lean_Parser_Term_binderIdent___elambda__1___rarg(x_3, x_4);
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
x_14 = l_Lean_Parser_ParserState_mkError(x_8, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_9);
lean::dec(x_3);
x_15 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean::dec(x_6);
return x_15;
}
}
}
obj* _init_l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_explicitBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_62 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_63 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
lean::inc(x_3);
x_64 = l_Lean_Parser_symbolFnAux(x_62, x_63, x_3, x_4);
x_65 = lean::cnstr_get(x_64, 3);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_67 = lean::array_get_size(x_66);
lean::dec(x_66);
lean::inc(x_3);
x_68 = l_Lean_Parser_Term_binderIdent___elambda__1___rarg(x_3, x_64);
x_69 = lean::cnstr_get(x_68, 3);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
x_70 = 0;
lean::inc(x_3);
x_71 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1(x_70, x_2, x_3, x_68);
x_72 = l_Lean_nullKind;
x_73 = l_Lean_Parser_ParserState_mkNode(x_71, x_72, x_67);
x_7 = x_73;
goto block_61;
}
else
{
obj* x_74; obj* x_75; 
lean::dec(x_69);
x_74 = l_Lean_nullKind;
x_75 = l_Lean_Parser_ParserState_mkNode(x_68, x_74, x_67);
x_7 = x_75;
goto block_61;
}
}
else
{
obj* x_76; obj* x_77; 
lean::dec(x_65);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_76 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_77 = l_Lean_Parser_ParserState_mkNode(x_64, x_76, x_6);
return x_77;
}
block_61:
{
obj* x_8; 
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_3);
x_10 = lean::apply_3(x_9, x_2, x_3, x_7);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_51; obj* x_52; 
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::array_get_size(x_12);
lean::dec(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::inc(x_3);
x_51 = l_Lean_Parser_Term_binderDefault___elambda__1___rarg(x_3, x_10);
x_52 = lean::cnstr_get(x_51, 3);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
x_15 = x_51;
goto block_50;
}
else
{
obj* x_53; uint8 x_54; 
lean::dec(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
x_54 = lean::nat_dec_eq(x_53, x_14);
lean::dec(x_53);
if (x_54 == 0)
{
x_15 = x_51;
goto block_50;
}
else
{
obj* x_55; obj* x_56; 
lean::inc(x_14);
x_55 = l_Lean_Parser_ParserState_restore(x_51, x_13, x_14);
lean::inc(x_3);
x_56 = l_Lean_Parser_Term_binderTactic___elambda__1___rarg(x_3, x_55);
x_15 = x_56;
goto block_50;
}
}
block_50:
{
obj* x_16; 
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_14);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_15, x_17, x_13);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_21 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_22 = l_Lean_Parser_symbolFnAux(x_20, x_21, x_3, x_18);
x_23 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_6);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::dec(x_3);
x_25 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_26 = l_Lean_Parser_ParserState_mkNode(x_18, x_25, x_6);
return x_26;
}
}
else
{
obj* x_27; uint8 x_28; 
lean::dec(x_16);
x_27 = lean::cnstr_get(x_15, 1);
lean::inc(x_27);
x_28 = lean::nat_dec_eq(x_27, x_14);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_14);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_15, x_29, x_13);
x_31 = lean::cnstr_get(x_30, 3);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_33 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_34 = l_Lean_Parser_symbolFnAux(x_32, x_33, x_3, x_30);
x_35 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_6);
return x_36;
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_31);
lean::dec(x_3);
x_37 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_38 = l_Lean_Parser_ParserState_mkNode(x_30, x_37, x_6);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = l_Lean_Parser_ParserState_restore(x_15, x_13, x_14);
x_40 = l_Lean_nullKind;
x_41 = l_Lean_Parser_ParserState_mkNode(x_39, x_40, x_13);
x_42 = lean::cnstr_get(x_41, 3);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_43 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_44 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_45 = l_Lean_Parser_symbolFnAux(x_43, x_44, x_3, x_41);
x_46 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_47 = l_Lean_Parser_ParserState_mkNode(x_45, x_46, x_6);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
lean::dec(x_42);
lean::dec(x_3);
x_48 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_49 = l_Lean_Parser_ParserState_mkNode(x_41, x_48, x_6);
return x_49;
}
}
}
}
}
else
{
obj* x_57; obj* x_58; 
lean::dec(x_11);
lean::dec(x_3);
x_57 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_58 = l_Lean_Parser_ParserState_mkNode(x_10, x_57, x_6);
return x_58;
}
}
else
{
obj* x_59; obj* x_60; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_59 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1;
x_60 = l_Lean_Parser_ParserState_mkNode(x_7, x_59, x_6);
return x_60;
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
obj* l_Lean_Parser_Term_explicitBinder(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = l_Lean_Parser_Term_binderType(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Parser_Term_explicitBinder___closed__1;
x_5 = l_Lean_Parser_andthenInfo(x_3, x_4);
x_6 = l_Lean_Parser_Term_explicitBinder___closed__2;
x_7 = l_Lean_Parser_andthenInfo(x_6, x_5);
x_8 = l_Lean_Parser_Term_explicitBinder___closed__3;
x_9 = l_Lean_Parser_andthenInfo(x_8, x_7);
x_10 = l_Lean_Parser_nodeInfo(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_explicitBinder___elambda__1), 4, 1);
lean::closure_set(x_11, 0, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
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
obj* _init_l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_implicitBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_Term_structInst___elambda__1___closed__1;
x_8 = l_Lean_Parser_Term_structInst___elambda__1___closed__2;
lean::inc(x_3);
x_9 = l_Lean_Parser_symbolFnAux(x_7, x_8, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
lean::inc(x_3);
x_13 = l_Lean_Parser_Term_binderIdent___elambda__1___rarg(x_3, x_9);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = 0;
lean::inc(x_3);
x_16 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1(x_15, x_2, x_3, x_13);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_12);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
lean::dec(x_1);
lean::inc(x_3);
x_21 = lean::apply_3(x_20, x_2, x_3, x_18);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_24 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_25 = l_Lean_Parser_symbolFnAux(x_23, x_24, x_3, x_21);
x_26 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_6);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_3);
x_28 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_29 = l_Lean_Parser_ParserState_mkNode(x_21, x_28, x_6);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_30 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_31 = l_Lean_Parser_ParserState_mkNode(x_18, x_30, x_6);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_14);
x_32 = l_Lean_nullKind;
x_33 = l_Lean_Parser_ParserState_mkNode(x_13, x_32, x_12);
x_34 = lean::cnstr_get(x_33, 3);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_1, 1);
lean::inc(x_35);
lean::dec(x_1);
lean::inc(x_3);
x_36 = lean::apply_3(x_35, x_2, x_3, x_33);
x_37 = lean::cnstr_get(x_36, 3);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = l_Lean_Parser_Term_id___elambda__1___closed__4;
x_39 = l_Lean_Parser_Term_id___elambda__1___closed__5;
x_40 = l_Lean_Parser_symbolFnAux(x_38, x_39, x_3, x_36);
x_41 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_6);
return x_42;
}
else
{
obj* x_43; obj* x_44; 
lean::dec(x_37);
lean::dec(x_3);
x_43 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_44 = l_Lean_Parser_ParserState_mkNode(x_36, x_43, x_6);
return x_44;
}
}
else
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_45 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_46 = l_Lean_Parser_ParserState_mkNode(x_33, x_45, x_6);
return x_46;
}
}
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_47 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
x_48 = l_Lean_Parser_ParserState_mkNode(x_9, x_47, x_6);
return x_48;
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
obj* l_Lean_Parser_Term_implicitBinder(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = l_Lean_Parser_Term_binderType(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Parser_Term_implicitBinder___closed__1;
x_5 = l_Lean_Parser_andthenInfo(x_3, x_4);
x_6 = l_Lean_Parser_Term_explicitBinder___closed__2;
x_7 = l_Lean_Parser_andthenInfo(x_6, x_5);
x_8 = l_Lean_Parser_Term_implicitBinder___closed__2;
x_9 = l_Lean_Parser_andthenInfo(x_8, x_7);
x_10 = l_Lean_Parser_nodeInfo(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_implicitBinder___elambda__1), 4, 1);
lean::closure_set(x_11, 0, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
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
obj* _init_l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1() {
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
x_8 = lean::mk_string("instBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_instBinder___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_list___elambda__1___closed__1;
x_6 = l_Lean_Parser_Term_list___elambda__1___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::inc(x_1);
x_9 = l_Lean_Parser_Term_optIdent___elambda__1___rarg(x_1, x_7);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_12 = l_Lean_Parser_builtinTermParsingTable;
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_14 = l_Lean_Parser_runBuiltinParserUnsafe(x_11, x_12, x_13, x_1, x_9);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = l_Lean_Parser_Term_list___elambda__1___closed__4;
x_17 = l_Lean_Parser_Term_list___elambda__1___closed__5;
x_18 = l_Lean_Parser_symbolFnAux(x_16, x_17, x_1, x_14);
x_19 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_4);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_15);
lean::dec(x_1);
x_21 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
x_22 = l_Lean_Parser_ParserState_mkNode(x_14, x_21, x_4);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_1);
x_23 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
x_24 = l_Lean_Parser_ParserState_mkNode(x_9, x_23, x_4);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_8);
lean::dec(x_1);
x_25 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1;
x_26 = l_Lean_Parser_ParserState_mkNode(x_7, x_25, x_4);
return x_26;
}
}
}
obj* l_Lean_Parser_Term_instBinder___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_instBinder___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_instBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::box(0);
x_2 = lean::mk_string("[");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("]");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolInfo(x_9, x_1);
x_11 = l_Lean_Parser_andthenInfo(x_7, x_10);
x_12 = l_Lean_Parser_Term_optIdent;
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = l_Lean_Parser_andthenInfo(x_13, x_11);
x_15 = l_Lean_Parser_andthenInfo(x_4, x_14);
x_16 = l_Lean_Parser_nodeInfo(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_instBinder___elambda__1___boxed), 1, 0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* l_Lean_Parser_Term_instBinder___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_instBinder___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Term_bracktedBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::array_get_size(x_7);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::inc(x_4);
lean::inc(x_3);
x_10 = lean::apply_3(x_6, x_3, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_12; uint8 x_13; 
lean::dec(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_13 = lean::nat_dec_eq(x_12, x_9);
lean::dec(x_12);
if (x_13 == 0)
{
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::inc(x_9);
x_14 = l_Lean_Parser_ParserState_restore(x_10, x_8, x_9);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
x_17 = lean::array_get_size(x_16);
lean::dec(x_16);
lean::inc(x_4);
x_18 = lean::apply_3(x_15, x_3, x_4, x_14);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
lean::dec(x_17);
lean::dec(x_9);
lean::dec(x_4);
return x_18;
}
else
{
obj* x_20; uint8 x_21; 
lean::dec(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
x_21 = lean::nat_dec_eq(x_20, x_9);
lean::dec(x_20);
if (x_21 == 0)
{
lean::dec(x_17);
lean::dec(x_9);
lean::dec(x_4);
return x_18;
}
else
{
obj* x_22; obj* x_23; 
x_22 = l_Lean_Parser_ParserState_restore(x_18, x_17, x_9);
lean::dec(x_17);
x_23 = l_Lean_Parser_Term_instBinder___elambda__1___rarg(x_4, x_22);
return x_23;
}
}
}
}
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
obj* l_Lean_Parser_Term_bracktedBinder(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = l_Lean_Parser_Term_explicitBinder(x_1);
x_3 = l_Lean_Parser_Term_implicitBinder(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_Term_bracktedBinder___closed__1;
x_6 = l_Lean_Parser_orelseInfo(x_4, x_5);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = l_Lean_Parser_orelseInfo(x_7, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracktedBinder___elambda__1), 5, 2);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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
obj* _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" → ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" -> ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string(" → ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string(" -> ");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = lean::mk_string("expected '");
x_6 = lean::string_append(x_5, x_2);
lean::dec(x_2);
x_7 = lean::mk_string("' or '");
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
x_9 = lean::string_append(x_8, x_4);
lean::dec(x_4);
x_10 = lean::mk_string("'");
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" → ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("found '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("' as expected, but brackets are needed");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__5() {
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
obj* l_Lean_Parser_Term_depArrow___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = 1;
x_5 = l_Lean_Parser_Term_bracktedBinder(x_4);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
lean::inc(x_2);
lean::inc(x_1);
x_9 = lean::apply_3(x_8, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = l_Lean_Parser_Term_depArrow___elambda__1___closed__1;
x_12 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_13 = lean::mk_nat_obj(25u);
x_14 = l_Lean_Parser_Term_depArrow___elambda__1___closed__3;
x_15 = l_Lean_Parser_Term_depArrow___elambda__1___closed__4;
lean::inc(x_2);
x_16 = l_Lean_Parser_unicodeSymbolCheckPrecFnAux(x_11, x_12, x_13, x_14, x_15, x_1, x_2, x_9);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_19 = l_Lean_Parser_builtinTermParsingTable;
x_20 = lean::mk_nat_obj(0u);
x_21 = l_Lean_Parser_runBuiltinParserUnsafe(x_18, x_19, x_20, x_2, x_16);
x_22 = l_Lean_Parser_Term_depArrow___elambda__1___closed__5;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_7);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_17);
lean::dec(x_2);
x_24 = l_Lean_Parser_Term_depArrow___elambda__1___closed__5;
x_25 = l_Lean_Parser_ParserState_mkNode(x_16, x_24, x_7);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_1);
x_26 = l_Lean_Parser_Term_depArrow___elambda__1___closed__5;
x_27 = l_Lean_Parser_ParserState_mkNode(x_9, x_26, x_7);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_Term_depArrow() {
_start:
{
uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = 1;
x_2 = l_Lean_Parser_Term_bracktedBinder(x_1);
x_3 = lean::mk_string(" → ");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = lean::mk_string(" -> ");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
x_7 = lean::mk_nat_obj(25u);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = l_Lean_Parser_unicodeSymbolInfo(x_4, x_6, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_11 = lean::box(1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_andthenInfo(x_9, x_12);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_15 = l_Lean_Parser_andthenInfo(x_14, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_depArrow___elambda__1), 3, 0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_depArrow(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_depArrow___elambda__1___closed__5;
x_4 = l_Lean_Parser_Term_depArrow;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1() {
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
x_8 = lean::mk_string("simpleBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_simpleBinder___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_2);
x_6 = l_Lean_Parser_Term_binderIdent___elambda__1___rarg(x_2, x_3);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = 0;
x_9 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_explicitBinder___elambda__1___spec__1(x_8, x_1, x_2, x_6);
x_10 = l_Lean_nullKind;
lean::inc(x_5);
x_11 = l_Lean_Parser_ParserState_mkNode(x_9, x_10, x_5);
x_12 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_5);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_7);
lean::dec(x_2);
x_14 = l_Lean_nullKind;
lean::inc(x_5);
x_15 = l_Lean_Parser_ParserState_mkNode(x_6, x_14, x_5);
x_16 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_5);
return x_17;
}
}
}
obj* _init_l_Lean_Parser_Term_simpleBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Term_binderIdent;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_nodeInfo(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_simpleBinder___elambda__1___boxed), 3, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Term_simpleBinder___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_simpleBinder___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_4);
x_10 = l_Lean_Parser_Term_simpleBinder___elambda__1(x_3, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; uint8 x_13; 
lean::dec(x_9);
lean::dec(x_7);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_13 = lean::nat_dec_eq(x_8, x_12);
lean::dec(x_12);
lean::dec(x_8);
if (x_13 == 0)
{
x_5 = x_10;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_15 = l_Lean_Parser_manyAux___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkError(x_10, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_11);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_18 = lean::nat_dec_eq(x_17, x_8);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; 
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_19 = l_Lean_Parser_ParserState_restore(x_10, x_7, x_8);
lean::dec(x_7);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::inc(x_8);
x_20 = l_Lean_Parser_ParserState_restore(x_10, x_7, x_8);
lean::inc(x_4);
lean::inc(x_3);
x_21 = lean::apply_3(x_9, x_3, x_4, x_20);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; uint8 x_24; 
lean::dec(x_7);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
x_24 = lean::nat_dec_eq(x_8, x_23);
lean::dec(x_23);
lean::dec(x_8);
if (x_24 == 0)
{
x_5 = x_21;
goto _start;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_26 = l_Lean_Parser_manyAux___main___closed__1;
x_27 = l_Lean_Parser_ParserState_mkError(x_21, x_26);
return x_27;
}
}
else
{
obj* x_28; 
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_28 = l_Lean_Parser_ParserState_restore(x_21, x_7, x_8);
lean::dec(x_7);
return x_28;
}
}
}
}
}
obj* _init_l_Lean_Parser_Term_forall___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("∀");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_forall___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("forall");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_forall___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string("∀");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("forall");
x_4 = l_String_trim(x_3);
lean::dec(x_3);
x_5 = lean::mk_string("expected '");
x_6 = lean::string_append(x_5, x_2);
lean::dec(x_2);
x_7 = lean::mk_string("' or '");
x_8 = lean::string_append(x_6, x_7);
lean::dec(x_7);
x_9 = lean::string_append(x_8, x_4);
lean::dec(x_4);
x_10 = lean::mk_string("'");
x_11 = lean::string_append(x_9, x_10);
lean::dec(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Term_forall___elambda__1___closed__4() {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = 0;
x_2 = l_Lean_Parser_Term_bracktedBinder(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_forall___elambda__1___closed__5() {
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
obj* l_Lean_Parser_Term_forall___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = 0;
x_5 = l_Lean_Parser_Term_bracktedBinder(x_4);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
x_9 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_10 = l_Lean_Parser_Term_forall___elambda__1___closed__3;
lean::inc(x_2);
x_11 = l_Lean_Parser_unicodeSymbolFnAux(x_8, x_9, x_10, x_2, x_3);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = lean::array_get_size(x_13);
lean::dec(x_13);
x_55 = lean::cnstr_get(x_5, 1);
lean::inc(x_55);
lean::dec(x_5);
x_56 = lean::cnstr_get(x_11, 1);
lean::inc(x_56);
lean::inc(x_2);
x_57 = l_Lean_Parser_Term_simpleBinder___elambda__1(x_1, x_2, x_11);
x_58 = lean::cnstr_get(x_57, 3);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
lean::dec(x_56);
lean::dec(x_55);
x_15 = x_57;
goto block_54;
}
else
{
obj* x_59; uint8 x_60; 
lean::dec(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
x_60 = lean::nat_dec_eq(x_59, x_56);
lean::dec(x_59);
if (x_60 == 0)
{
lean::dec(x_56);
lean::dec(x_55);
x_15 = x_57;
goto block_54;
}
else
{
obj* x_61; obj* x_62; 
x_61 = l_Lean_Parser_ParserState_restore(x_57, x_14, x_56);
lean::inc(x_2);
lean::inc(x_1);
x_62 = lean::apply_3(x_55, x_1, x_2, x_61);
x_15 = x_62;
goto block_54;
}
}
block_54:
{
obj* x_16; 
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = l_Lean_Parser_Term_forall___elambda__1___closed__4;
x_18 = 0;
lean::inc(x_2);
x_19 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1(x_17, x_18, x_1, x_2, x_15);
x_20 = l_Lean_nullKind;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_14);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_24 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__1;
lean::inc(x_2);
x_25 = l_Lean_Parser_symbolFnAux(x_23, x_24, x_2, x_21);
x_26 = lean::cnstr_get(x_25, 3);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_28 = l_Lean_Parser_builtinTermParsingTable;
x_29 = lean::mk_nat_obj(0u);
x_30 = l_Lean_Parser_runBuiltinParserUnsafe(x_27, x_28, x_29, x_2, x_25);
x_31 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_7);
return x_32;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_26);
lean::dec(x_2);
x_33 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_34 = l_Lean_Parser_ParserState_mkNode(x_25, x_33, x_7);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_22);
lean::dec(x_2);
x_35 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_36 = l_Lean_Parser_ParserState_mkNode(x_21, x_35, x_7);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_16);
lean::dec(x_1);
x_37 = l_Lean_nullKind;
x_38 = l_Lean_Parser_ParserState_mkNode(x_15, x_37, x_14);
x_39 = lean::cnstr_get(x_38, 3);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_40 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_41 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__1;
lean::inc(x_2);
x_42 = l_Lean_Parser_symbolFnAux(x_40, x_41, x_2, x_38);
x_43 = lean::cnstr_get(x_42, 3);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_45 = l_Lean_Parser_builtinTermParsingTable;
x_46 = lean::mk_nat_obj(0u);
x_47 = l_Lean_Parser_runBuiltinParserUnsafe(x_44, x_45, x_46, x_2, x_42);
x_48 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_49 = l_Lean_Parser_ParserState_mkNode(x_47, x_48, x_7);
return x_49;
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_43);
lean::dec(x_2);
x_50 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_51 = l_Lean_Parser_ParserState_mkNode(x_42, x_50, x_7);
return x_51;
}
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_39);
lean::dec(x_2);
x_52 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_53 = l_Lean_Parser_ParserState_mkNode(x_38, x_52, x_7);
return x_53;
}
}
}
}
else
{
obj* x_63; obj* x_64; 
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_63 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_64 = l_Lean_Parser_ParserState_mkNode(x_11, x_63, x_7);
return x_64;
}
}
}
obj* _init_l_Lean_Parser_Term_forall() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_1 = lean::box(0);
x_2 = lean::mk_string("∀");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::mk_string("forall");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_unicodeSymbolInfo(x_3, x_5, x_1);
x_7 = 0;
x_8 = l_Lean_Parser_Term_bracktedBinder(x_7);
x_9 = l_Lean_Parser_Term_simpleBinder;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_12 = l_Lean_Parser_orelseInfo(x_10, x_11);
x_13 = lean::mk_string(", ");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
x_15 = l_Lean_Parser_symbolInfo(x_14, x_1);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_17 = lean::box(1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_andthenInfo(x_15, x_18);
x_20 = l_Lean_Parser_andthenInfo(x_12, x_19);
x_21 = l_Lean_Parser_andthenInfo(x_6, x_20);
x_22 = l_Lean_Parser_nodeInfo(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_forall___elambda__1), 3, 0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_forall(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_forall___elambda__1___closed__5;
x_4 = l_Lean_Parser_Term_forall;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_equation___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" | ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_equation___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" | ");
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
obj* _init_l_Lean_Parser_Term_equation___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" => ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_equation___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" => ");
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
obj* _init_l_Lean_Parser_Term_equation___elambda__1___closed__5() {
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
x_8 = lean::mk_string("equation");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_equation___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_equation___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_equation___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_11 = 0;
x_12 = 0;
lean::inc(x_2);
x_13 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(x_10, x_11, x_12, x_1, x_2, x_8);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = l_Lean_Parser_Term_equation___elambda__1___closed__3;
x_16 = l_Lean_Parser_Term_equation___elambda__1___closed__4;
lean::inc(x_2);
x_17 = l_Lean_Parser_symbolFnAux(x_15, x_16, x_2, x_13);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_20 = l_Lean_Parser_builtinTermParsingTable;
x_21 = lean::mk_nat_obj(0u);
x_22 = l_Lean_Parser_runBuiltinParserUnsafe(x_19, x_20, x_21, x_2, x_17);
x_23 = l_Lean_Parser_Term_equation___elambda__1___closed__5;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_5);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_18);
lean::dec(x_2);
x_25 = l_Lean_Parser_Term_equation___elambda__1___closed__5;
x_26 = l_Lean_Parser_ParserState_mkNode(x_17, x_25, x_5);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_14);
lean::dec(x_2);
x_27 = l_Lean_Parser_Term_equation___elambda__1___closed__5;
x_28 = l_Lean_Parser_ParserState_mkNode(x_13, x_27, x_5);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_9);
lean::dec(x_2);
x_29 = l_Lean_Parser_Term_equation___elambda__1___closed__5;
x_30 = l_Lean_Parser_ParserState_mkNode(x_8, x_29, x_5);
return x_30;
}
}
}
obj* _init_l_Lean_Parser_Term_equation() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" | ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string(", ");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolInfo(x_9, x_1);
lean::inc(x_7);
x_11 = l_Lean_Parser_sepBy1Info(x_7, x_10);
x_12 = lean::mk_string(" => ");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_1);
x_15 = l_Lean_Parser_andthenInfo(x_14, x_7);
x_16 = l_Lean_Parser_andthenInfo(x_11, x_15);
x_17 = l_Lean_Parser_andthenInfo(x_4, x_16);
x_18 = l_Lean_Parser_nodeInfo(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_equation___elambda__1___boxed), 3, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_Term_equation___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_equation___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_match___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_8 = l_Lean_Parser_Term_equation___elambda__1(x_2, x_3, x_4);
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
x_14 = l_Lean_Parser_ParserState_mkError(x_8, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_9);
lean::dec(x_3);
x_15 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean::dec(x_6);
return x_15;
}
}
}
obj* _init_l_Lean_Parser_Term_match___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("match ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_match___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("match ");
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
obj* _init_l_Lean_Parser_Term_match___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(" with ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_match___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(" with ");
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
obj* _init_l_Lean_Parser_Term_match___elambda__1___closed__5() {
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
obj* l_Lean_Parser_Term_match___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Term_match___elambda__1___closed__1;
x_7 = l_Lean_Parser_Term_match___elambda__1___closed__2;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = l_Lean_Parser_Term_id___elambda__1___closed__3;
x_11 = 0;
x_12 = 0;
lean::inc(x_2);
x_13 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Term_tupleTail___elambda__1___spec__1(x_10, x_11, x_12, x_1, x_2, x_8);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
lean::inc(x_2);
x_15 = l_Lean_Parser_Term_optType___elambda__1___rarg(x_2, x_13);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = l_Lean_Parser_Term_match___elambda__1___closed__3;
x_18 = l_Lean_Parser_Term_match___elambda__1___closed__4;
lean::inc(x_2);
x_19 = l_Lean_Parser_symbolFnAux(x_17, x_18, x_2, x_15);
x_20 = lean::cnstr_get(x_19, 3);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
x_22 = lean::array_get_size(x_21);
lean::dec(x_21);
lean::inc(x_2);
x_23 = l_Lean_Parser_Term_equation___elambda__1(x_1, x_2, x_19);
x_24 = lean::cnstr_get(x_23, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_match___elambda__1___spec__1(x_11, x_1, x_2, x_23);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_22);
x_28 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_5);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_24);
lean::dec(x_2);
x_30 = l_Lean_nullKind;
x_31 = l_Lean_Parser_ParserState_mkNode(x_23, x_30, x_22);
x_32 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_33 = l_Lean_Parser_ParserState_mkNode(x_31, x_32, x_5);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
lean::dec(x_20);
lean::dec(x_2);
x_34 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_35 = l_Lean_Parser_ParserState_mkNode(x_19, x_34, x_5);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_16);
lean::dec(x_2);
x_36 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_37 = l_Lean_Parser_ParserState_mkNode(x_15, x_36, x_5);
return x_37;
}
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_14);
lean::dec(x_2);
x_38 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_39 = l_Lean_Parser_ParserState_mkNode(x_13, x_38, x_5);
return x_39;
}
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_9);
lean::dec(x_2);
x_40 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_41 = l_Lean_Parser_ParserState_mkNode(x_8, x_40, x_5);
return x_41;
}
}
}
obj* _init_l_Lean_Parser_Term_match() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_1 = lean::box(0);
x_2 = lean::mk_string("match ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string(", ");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_symbolInfo(x_9, x_1);
x_11 = l_Lean_Parser_sepBy1Info(x_7, x_10);
x_12 = lean::mk_string(" with ");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_1);
x_15 = l_Lean_Parser_Term_equation;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = l_Lean_Parser_andthenInfo(x_14, x_16);
x_18 = l_Lean_Parser_Term_optType;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = l_Lean_Parser_andthenInfo(x_19, x_17);
x_21 = l_Lean_Parser_andthenInfo(x_11, x_20);
x_22 = l_Lean_Parser_andthenInfo(x_4, x_21);
x_23 = l_Lean_Parser_nodeInfo(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_match___elambda__1___boxed), 3, 0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_match___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_match___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Term_match___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Term_match___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_match(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_match___elambda__1___closed__5;
x_4 = l_Lean_Parser_Term_match;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("nomatch ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("nomatch ");
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
obj* _init_l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3() {
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
obj* l_Lean_Parser_Term_nomatch___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__1;
x_6 = l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Term_nomatch___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_nomatch___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_nomatch() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("nomatch ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_andthenInfo(x_4, x_7);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_nomatch___elambda__1___boxed), 1, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Term_nomatch___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_nomatch___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_nomatch(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3;
x_4 = l_Lean_Parser_Term_nomatch;
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1() {
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
x_8 = lean::mk_string("namedArgument");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Term_namedArgument___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::array_get_size(x_3);
lean::dec(x_3);
x_27 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__1;
x_28 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_29 = l_Lean_Parser_symbolFnAux(x_27, x_28, x_1, x_2);
x_30 = lean::cnstr_get(x_29, 3);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; 
lean::inc(x_1);
x_31 = l_Lean_Parser_identFn___rarg(x_1, x_29);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1;
x_34 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2;
lean::inc(x_1);
x_35 = l_Lean_Parser_symbolFnAux(x_33, x_34, x_1, x_31);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 2);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 3);
lean::inc(x_38);
x_6 = x_35;
x_7 = x_36;
x_8 = x_37;
x_9 = x_38;
goto block_26;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_31, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_31, 2);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_31, 3);
lean::inc(x_41);
x_6 = x_31;
x_7 = x_39;
x_8 = x_40;
x_9 = x_41;
goto block_26;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_30);
x_42 = lean::cnstr_get(x_29, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_29, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_29, 3);
lean::inc(x_44);
x_6 = x_29;
x_7 = x_42;
x_8 = x_43;
x_9 = x_44;
goto block_26;
}
block_26:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
x_10 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_11 = l_Lean_Parser_builtinTermParsingTable;
x_12 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_13 = l_Lean_Parser_runBuiltinParserUnsafe(x_10, x_11, x_12, x_1, x_6);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_16 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_17 = l_Lean_Parser_symbolFnAux(x_15, x_16, x_1, x_13);
x_18 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
return x_19;
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_14);
lean::dec(x_1);
x_20 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1;
x_21 = l_Lean_Parser_ParserState_mkNode(x_13, x_20, x_5);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_6);
lean::dec(x_1);
x_22 = l_Array_shrink___main___rarg(x_7, x_5);
x_23 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_4);
lean::cnstr_set(x_23, 2, x_8);
lean::cnstr_set(x_23, 3, x_9);
x_24 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
}
}
obj* l_Lean_Parser_Term_namedArgument___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_namedArgument___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_namedArgument() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::box(0);
x_2 = lean::mk_string("(");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_3, x_1);
x_5 = lean::mk_string("ident");
x_6 = l_Lean_Parser_mkAtomicInfo(x_5);
x_7 = lean::mk_string(" := ");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_symbolInfo(x_8, x_1);
x_10 = l_Lean_Parser_andthenInfo(x_6, x_9);
x_11 = l_Lean_Parser_andthenInfo(x_4, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_13 = lean::box(1);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::mk_string(")");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
x_17 = l_Lean_Parser_symbolInfo(x_16, x_1);
x_18 = l_Lean_Parser_andthenInfo(x_14, x_17);
x_19 = l_Lean_Parser_andthenInfo(x_11, x_18);
x_20 = l_Lean_Parser_nodeInfo(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_namedArgument___elambda__1___boxed), 1, 0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
obj* l_Lean_Parser_Term_namedArgument___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Term_namedArgument___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Term_app___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_app___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_3);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
lean::inc(x_2);
x_11 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg(x_2, x_6);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_2);
x_13 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_14 = l_Lean_Parser_ParserState_mkNode(x_11, x_13, x_5);
return x_14;
}
else
{
obj* x_15; uint8 x_16; 
lean::dec(x_12);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
x_16 = lean::nat_dec_eq(x_15, x_10);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_2);
x_17 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_18 = l_Lean_Parser_ParserState_mkNode(x_11, x_17, x_5);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean::dec(x_9);
x_20 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_21 = l_Lean_Parser_builtinTermParsingTable;
x_22 = l_Lean_Parser_appPrec;
x_23 = l_Lean_Parser_runBuiltinParserUnsafe(x_20, x_21, x_22, x_2, x_19);
x_24 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_26 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_27 = l_Lean_Parser_ParserState_mkNode(x_6, x_26, x_5);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_Term_app() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_2 = lean::box(1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_Term_namedArgument;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_orelseInfo(x_5, x_3);
x_7 = l_Lean_Parser_epsilonInfo;
x_8 = l_Lean_Parser_andthenInfo(x_7, x_6);
x_9 = l_Lean_Parser_nodeInfo(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_app___elambda__1), 3, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_app(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_app;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_proj___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string(".");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("' without whitespaces arount it");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_proj___elambda__1___closed__2() {
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
obj* _init_l_Lean_Parser_Term_proj___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string(".");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Term_proj___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = l_Lean_Parser_checkTailNoWs(x_1);
lean::dec(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_10 = l_Lean_Parser_ParserState_mkError(x_6, x_9);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::array_get_size(x_12);
lean::dec(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
x_15 = l_Lean_Parser_fieldIdxFn(x_2, x_10);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_2);
x_17 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_15, x_17, x_5);
return x_18;
}
else
{
obj* x_19; uint8 x_20; 
lean::dec(x_16);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_20 = lean::nat_dec_eq(x_19, x_14);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_2);
x_21 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_15, x_21, x_5);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = l_Lean_Parser_ParserState_restore(x_15, x_13, x_14);
lean::dec(x_13);
x_24 = l_Lean_Parser_identFn___rarg(x_2, x_23);
x_25 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_5);
return x_26;
}
}
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_11);
lean::dec(x_2);
x_27 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_28 = l_Lean_Parser_ParserState_mkNode(x_10, x_27, x_5);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = l_Lean_Parser_Term_proj___elambda__1___closed__3;
x_30 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_31 = lean::mk_nat_obj(0u);
x_32 = l_Lean_Parser_strAux___main(x_29, x_30, x_31, x_2, x_6);
x_33 = lean::cnstr_get(x_32, 3);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_32, 0);
lean::inc(x_34);
x_35 = lean::array_get_size(x_34);
lean::dec(x_34);
x_36 = lean::cnstr_get(x_32, 1);
lean::inc(x_36);
x_37 = l_Lean_Parser_fieldIdxFn(x_2, x_32);
x_38 = lean::cnstr_get(x_37, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_36);
lean::dec(x_35);
lean::dec(x_2);
x_39 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_40 = l_Lean_Parser_ParserState_mkNode(x_37, x_39, x_5);
return x_40;
}
else
{
obj* x_41; uint8 x_42; 
lean::dec(x_38);
x_41 = lean::cnstr_get(x_37, 1);
lean::inc(x_41);
x_42 = lean::nat_dec_eq(x_41, x_36);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; 
lean::dec(x_36);
lean::dec(x_35);
lean::dec(x_2);
x_43 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_44 = l_Lean_Parser_ParserState_mkNode(x_37, x_43, x_5);
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = l_Lean_Parser_ParserState_restore(x_37, x_35, x_36);
lean::dec(x_35);
x_46 = l_Lean_Parser_identFn___rarg(x_2, x_45);
x_47 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_5);
return x_48;
}
}
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_33);
lean::dec(x_2);
x_49 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_50 = l_Lean_Parser_ParserState_mkNode(x_32, x_49, x_5);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_51 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_52 = l_Lean_Parser_ParserState_mkNode(x_6, x_51, x_5);
return x_52;
}
}
}
obj* _init_l_Lean_Parser_Term_proj() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string(".");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_symbolNoWsInfo(x_6, x_4);
x_8 = lean::mk_string("fieldIdx");
x_9 = l_Lean_Parser_mkAtomicInfo(x_8);
x_10 = lean::mk_string("ident");
x_11 = l_Lean_Parser_mkAtomicInfo(x_10);
x_12 = l_Lean_Parser_orelseInfo(x_9, x_11);
x_13 = l_Lean_Parser_andthenInfo(x_7, x_12);
x_14 = l_Lean_Parser_epsilonInfo;
x_15 = l_Lean_Parser_andthenInfo(x_14, x_13);
x_16 = l_Lean_Parser_nodeInfo(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_proj___elambda__1), 3, 0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_proj(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_4 = l_Lean_Parser_Term_proj;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_arrow___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_arrow___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::mk_string(" → ");
x_5 = lean::mk_string(" -> ");
x_6 = lean::mk_nat_obj(25u);
x_7 = l_Lean_Parser_Term_unicodeInfixR(x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::apply_3(x_8, x_1, x_2, x_3);
x_12 = l_Lean_Parser_Term_arrow___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_10);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_arrow() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string(" → ");
x_2 = lean::mk_string(" -> ");
x_3 = lean::mk_nat_obj(25u);
x_4 = l_Lean_Parser_Term_unicodeInfixR(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_arrow___elambda__1), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_arrow(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_arrow___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_arrow;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_array___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("[");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_3 = lean::mk_string("expected '");
x_4 = lean::string_append(x_3, x_2);
lean::dec(x_2);
x_5 = lean::mk_string("' without whitespaces arount it");
x_6 = lean::string_append(x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_array___elambda__1___closed__2() {
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
obj* l_Lean_Parser_Term_array___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = l_Lean_Parser_checkTailNoWs(x_1);
lean::dec(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = l_Lean_Parser_Term_array___elambda__1___closed__1;
x_10 = l_Lean_Parser_ParserState_mkError(x_6, x_9);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_13 = l_Lean_Parser_builtinTermParsingTable;
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_15 = l_Lean_Parser_runBuiltinParserUnsafe(x_12, x_13, x_14, x_2, x_10);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = l_Lean_Parser_Term_list___elambda__1___closed__4;
x_18 = l_Lean_Parser_Term_list___elambda__1___closed__5;
x_19 = l_Lean_Parser_symbolFnAux(x_17, x_18, x_2, x_15);
x_20 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_5);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_16);
lean::dec(x_2);
x_22 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_23 = l_Lean_Parser_ParserState_mkNode(x_15, x_22, x_5);
return x_23;
}
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_2);
x_24 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_10, x_24, x_5);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = l_Lean_Parser_Term_list___elambda__1___closed__1;
x_27 = l_Lean_Parser_Term_array___elambda__1___closed__1;
x_28 = lean::mk_nat_obj(0u);
x_29 = l_Lean_Parser_strAux___main(x_26, x_27, x_28, x_2, x_6);
x_30 = lean::cnstr_get(x_29, 3);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_32 = l_Lean_Parser_builtinTermParsingTable;
lean::inc(x_2);
x_33 = l_Lean_Parser_runBuiltinParserUnsafe(x_31, x_32, x_28, x_2, x_29);
x_34 = lean::cnstr_get(x_33, 3);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = l_Lean_Parser_Term_list___elambda__1___closed__4;
x_36 = l_Lean_Parser_Term_list___elambda__1___closed__5;
x_37 = l_Lean_Parser_symbolFnAux(x_35, x_36, x_2, x_33);
x_38 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_39 = l_Lean_Parser_ParserState_mkNode(x_37, x_38, x_5);
return x_39;
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_34);
lean::dec(x_2);
x_40 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_41 = l_Lean_Parser_ParserState_mkNode(x_33, x_40, x_5);
return x_41;
}
}
else
{
obj* x_42; obj* x_43; 
lean::dec(x_30);
lean::dec(x_2);
x_42 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_43 = l_Lean_Parser_ParserState_mkNode(x_29, x_42, x_5);
return x_43;
}
}
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_44 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_45 = l_Lean_Parser_ParserState_mkNode(x_6, x_44, x_5);
return x_45;
}
}
}
obj* _init_l_Lean_Parser_Term_array() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = l_Lean_Parser_appPrec;
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string("[");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_symbolNoWsInfo(x_6, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_9 = lean::box(1);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(0);
x_12 = lean::mk_string("]");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = l_Lean_Parser_symbolInfo(x_13, x_11);
x_15 = l_Lean_Parser_andthenInfo(x_10, x_14);
x_16 = l_Lean_Parser_andthenInfo(x_7, x_15);
x_17 = l_Lean_Parser_epsilonInfo;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_16);
x_19 = l_Lean_Parser_nodeInfo(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_array___elambda__1), 3, 0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_array(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_array___elambda__1___closed__2;
x_4 = l_Lean_Parser_Term_array;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_fcomp___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_fcomp___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" ∘ ");
x_5 = lean::mk_nat_obj(90u);
x_6 = l_Lean_Parser_Term_infixR(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_fcomp___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_fcomp() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" ∘ ");
x_2 = lean::mk_nat_obj(90u);
x_3 = l_Lean_Parser_Term_infixR(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_fcomp___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_fcomp(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_fcomp___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_fcomp;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_add___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_add___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" + ");
x_5 = lean::mk_nat_obj(65u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_add___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_add() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" + ");
x_2 = lean::mk_nat_obj(65u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_add___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_add(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_add___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_add;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_sub___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_sub___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" - ");
x_5 = lean::mk_nat_obj(65u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_sub___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_sub() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" - ");
x_2 = lean::mk_nat_obj(65u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_sub___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_sub(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_sub___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_sub;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_mul___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_mul___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" * ");
x_5 = lean::mk_nat_obj(70u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_mul___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_mul() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" * ");
x_2 = lean::mk_nat_obj(70u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_mul___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_mul(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_mul___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_mul;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_div___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_div___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" / ");
x_5 = lean::mk_nat_obj(70u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_div___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_div() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" / ");
x_2 = lean::mk_nat_obj(70u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_div___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_div(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_div___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_div;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_mod___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_mod___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" % ");
x_5 = lean::mk_nat_obj(70u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_mod___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_mod() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" % ");
x_2 = lean::mk_nat_obj(70u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_mod___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_mod(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_mod___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_mod;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_modN___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_modN___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" %ₙ ");
x_5 = lean::mk_nat_obj(70u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_modN___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_modN() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" %ₙ ");
x_2 = lean::mk_nat_obj(70u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_modN___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_modN(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_modN___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_modN;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_le___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_le___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::mk_string(" ≤ ");
x_5 = lean::mk_string(" <= ");
x_6 = lean::mk_nat_obj(50u);
x_7 = l_Lean_Parser_Term_unicodeInfixL(x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::apply_3(x_8, x_1, x_2, x_3);
x_12 = l_Lean_Parser_Term_le___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_10);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_le() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string(" ≤ ");
x_2 = lean::mk_string(" <= ");
x_3 = lean::mk_nat_obj(50u);
x_4 = l_Lean_Parser_Term_unicodeInfixL(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_le___elambda__1), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_le(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_le___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_le;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_ge___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_ge___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::mk_string(" ≥ ");
x_5 = lean::mk_string(" >= ");
x_6 = lean::mk_nat_obj(50u);
x_7 = l_Lean_Parser_Term_unicodeInfixL(x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::apply_3(x_8, x_1, x_2, x_3);
x_12 = l_Lean_Parser_Term_ge___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_10);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_ge() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string(" ≥ ");
x_2 = lean::mk_string(" >= ");
x_3 = lean::mk_nat_obj(50u);
x_4 = l_Lean_Parser_Term_unicodeInfixL(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_ge___elambda__1), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_ge(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_ge___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_ge;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_lt___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_lt___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" < ");
x_5 = lean::mk_nat_obj(50u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_lt___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_lt() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" < ");
x_2 = lean::mk_nat_obj(50u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_lt___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_lt(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_lt___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_lt;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_gt___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_gt___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" > ");
x_5 = lean::mk_nat_obj(50u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_gt___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_gt() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" > ");
x_2 = lean::mk_nat_obj(50u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_gt___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_gt(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_gt___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_gt;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_eq___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_eq___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" = ");
x_5 = lean::mk_nat_obj(50u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_eq___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_eq() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" = ");
x_2 = lean::mk_nat_obj(50u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_eq___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_eq(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_eq___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_eq;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_beq___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_beq___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::mk_string(" == ");
x_5 = lean::mk_nat_obj(50u);
x_6 = l_Lean_Parser_Term_infixL(x_4, x_5);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::apply_3(x_7, x_1, x_2, x_3);
x_11 = l_Lean_Parser_Term_beq___elambda__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Term_beq() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string(" == ");
x_2 = lean::mk_nat_obj(50u);
x_3 = l_Lean_Parser_Term_infixL(x_1, x_2);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_beq___elambda__1), 3, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_beq(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_beq___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_beq;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_and___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_and___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::mk_string(" ∧ ");
x_5 = lean::mk_string(" /\\ ");
x_6 = lean::mk_nat_obj(35u);
x_7 = l_Lean_Parser_Term_unicodeInfixR(x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::apply_3(x_8, x_1, x_2, x_3);
x_12 = l_Lean_Parser_Term_and___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_10);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_and() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string(" ∧ ");
x_2 = lean::mk_string(" /\\ ");
x_3 = lean::mk_nat_obj(35u);
x_4 = l_Lean_Parser_Term_unicodeInfixR(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_and___elambda__1), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_and(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_and___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_and;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_or___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_or___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::mk_string(" ∨ ");
x_5 = lean::mk_string(" \\/ ");
x_6 = lean::mk_nat_obj(30u);
x_7 = l_Lean_Parser_Term_unicodeInfixR(x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::apply_3(x_8, x_1, x_2, x_3);
x_12 = l_Lean_Parser_Term_or___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_10);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_or() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string(" ∨ ");
x_2 = lean::mk_string(" \\/ ");
x_3 = lean::mk_nat_obj(30u);
x_4 = l_Lean_Parser_Term_unicodeInfixR(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_or___elambda__1), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_or(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_or___elambda__1___closed__1;
x_4 = l_Lean_Parser_Term_or;
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_Term_iff___elambda__1___closed__1() {
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
obj* l_Lean_Parser_Term_iff___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::mk_string(" ↔ ");
x_5 = lean::mk_string(" <-> ");
x_6 = lean::mk_nat_obj(20u);
x_7 = l_Lean_Parser_Term_unicodeInfixL(x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = lean::apply_3(x_8, x_1, x_2, x_3);
x_12 = l_Lean_Parser_Term_iff___elambda__1___closed__1;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_10);
return x_13;
}
}
obj* _init_l_Lean_Parser_Term_iff() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::mk_string(" ↔ ");
x_2 = lean::mk_string(" <-> ");
x_3 = lean::mk_nat_obj(20u);
x_4 = l_Lean_Parser_Term_unicodeInfixL(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_nodeInfo(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_iff___elambda__1), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___regBuiltinParser_Lean_Parser_Term_iff(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_builtinTermParsingTable;
x_3 = l_Lean_Parser_Term_iff___elambda__1___closed__1;
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "unicodeInfixR"), 3, l_Lean_Parser_Term_unicodeInfixR___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "infixR"), 2, l_Lean_Parser_Term_infixR___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "unicodeInfixL"), 3, l_Lean_Parser_Term_unicodeInfixL___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "infixL"), 2, l_Lean_Parser_Term_infixL___boxed);
l_Lean_Parser_Term_id___elambda__1___closed__1 = _init_l_Lean_Parser_Term_id___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_id___elambda__1___closed__1);
l_Lean_Parser_Term_id___elambda__1___closed__2 = _init_l_Lean_Parser_Term_id___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_id___elambda__1___closed__2);
l_Lean_Parser_Term_id___elambda__1___closed__3 = _init_l_Lean_Parser_Term_id___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_id___elambda__1___closed__3);
l_Lean_Parser_Term_id___elambda__1___closed__4 = _init_l_Lean_Parser_Term_id___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_id___elambda__1___closed__4);
l_Lean_Parser_Term_id___elambda__1___closed__5 = _init_l_Lean_Parser_Term_id___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_id___elambda__1___closed__5);
l_Lean_Parser_Term_id___elambda__1___closed__6 = _init_l_Lean_Parser_Term_id___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Term_id___elambda__1___closed__6);
l_Lean_Parser_Term_id = _init_l_Lean_Parser_Term_id();
lean::mark_persistent(l_Lean_Parser_Term_id);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "id"), l_Lean_Parser_Term_id);
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
l_Lean_Parser_Term_type___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_type___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_type___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_type___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_type___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_type___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_type___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_type___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_type___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_type = _init_l_Lean_Parser_Term_type();
lean::mark_persistent(l_Lean_Parser_Term_type);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "type"), l_Lean_Parser_Term_type);
w = l___regBuiltinParser_Lean_Parser_Term_type(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sort___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_sort___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_sort___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_sort___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_sort = _init_l_Lean_Parser_Term_sort();
lean::mark_persistent(l_Lean_Parser_Term_sort);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sort"), l_Lean_Parser_Term_sort);
w = l___regBuiltinParser_Lean_Parser_Term_sort(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_hole = _init_l_Lean_Parser_Term_hole();
lean::mark_persistent(l_Lean_Parser_Term_hole);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "hole"), l_Lean_Parser_Term_hole);
w = l___regBuiltinParser_Lean_Parser_Term_hole(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_sorry = _init_l_Lean_Parser_Term_sorry();
lean::mark_persistent(l_Lean_Parser_Term_sorry);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sorry"), l_Lean_Parser_Term_sorry);
w = l___regBuiltinParser_Lean_Parser_Term_sorry(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_cdot___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_cdot = _init_l_Lean_Parser_Term_cdot();
lean::mark_persistent(l_Lean_Parser_Term_cdot);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "cdot"), l_Lean_Parser_Term_cdot);
w = l___regBuiltinParser_Lean_Parser_Term_cdot(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_typeAscription___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_typeAscription = _init_l_Lean_Parser_Term_typeAscription();
lean::mark_persistent(l_Lean_Parser_Term_typeAscription);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "typeAscription"), l_Lean_Parser_Term_typeAscription);
l_Lean_Parser_Term_tupleTail___elambda__1___closed__1 = _init_l_Lean_Parser_Term_tupleTail___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_tupleTail___elambda__1___closed__1);
l_Lean_Parser_Term_tupleTail___elambda__1___closed__2 = _init_l_Lean_Parser_Term_tupleTail___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_tupleTail___elambda__1___closed__2);
l_Lean_Parser_Term_tupleTail = _init_l_Lean_Parser_Term_tupleTail();
lean::mark_persistent(l_Lean_Parser_Term_tupleTail);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "tupleTail"), l_Lean_Parser_Term_tupleTail);
l_Lean_Parser_Term_parenSpecial = _init_l_Lean_Parser_Term_parenSpecial();
lean::mark_persistent(l_Lean_Parser_Term_parenSpecial);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "parenSpecial"), l_Lean_Parser_Term_parenSpecial);
l_Lean_Parser_Term_paren___elambda__1___closed__1 = _init_l_Lean_Parser_Term_paren___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_paren___elambda__1___closed__1);
l_Lean_Parser_Term_paren = _init_l_Lean_Parser_Term_paren();
lean::mark_persistent(l_Lean_Parser_Term_paren);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "paren"), l_Lean_Parser_Term_paren);
w = l___regBuiltinParser_Lean_Parser_Term_paren(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1 = _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__1);
l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2 = _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2);
l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__3 = _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__3);
l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__4 = _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__4);
l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5 = _init_l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__5);
l_Lean_Parser_Term_anonymousCtor = _init_l_Lean_Parser_Term_anonymousCtor();
lean::mark_persistent(l_Lean_Parser_Term_anonymousCtor);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "anonymousCtor"), l_Lean_Parser_Term_anonymousCtor);
w = l___regBuiltinParser_Lean_Parser_Term_anonymousCtor(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_optIdent = _init_l_Lean_Parser_Term_optIdent();
lean::mark_persistent(l_Lean_Parser_Term_optIdent);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "optIdent"), l_Lean_Parser_Term_optIdent);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__4);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__5);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__6();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__6);
l_Lean_Parser_Term_if___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Term_if___elambda__1___rarg___closed__7();
lean::mark_persistent(l_Lean_Parser_Term_if___elambda__1___rarg___closed__7);
l_Lean_Parser_Term_if = _init_l_Lean_Parser_Term_if();
lean::mark_persistent(l_Lean_Parser_Term_if);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "if"), l_Lean_Parser_Term_if);
w = l___regBuiltinParser_Lean_Parser_Term_if(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_fromTerm___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_fromTerm = _init_l_Lean_Parser_Term_fromTerm();
lean::mark_persistent(l_Lean_Parser_Term_fromTerm);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "fromTerm"), l_Lean_Parser_Term_fromTerm);
l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_haveAssign = _init_l_Lean_Parser_Term_haveAssign();
lean::mark_persistent(l_Lean_Parser_Term_haveAssign);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "haveAssign"), l_Lean_Parser_Term_haveAssign);
l_Lean_Parser_Term_have___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_have___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_have___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_have___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_have___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_have___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_have___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_have___elambda__1___rarg___closed__4);
l_Lean_Parser_Term_have___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Term_have___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_have___elambda__1___rarg___closed__5);
l_Lean_Parser_Term_have = _init_l_Lean_Parser_Term_have();
lean::mark_persistent(l_Lean_Parser_Term_have);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "have"), l_Lean_Parser_Term_have);
w = l___regBuiltinParser_Lean_Parser_Term_have(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_suffices___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_suffices = _init_l_Lean_Parser_Term_suffices();
lean::mark_persistent(l_Lean_Parser_Term_suffices);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "suffices"), l_Lean_Parser_Term_suffices);
w = l___regBuiltinParser_Lean_Parser_Term_suffices(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_show___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_show___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_show___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_show___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_show___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_show___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_show___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_show___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_show___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_show = _init_l_Lean_Parser_Term_show();
lean::mark_persistent(l_Lean_Parser_Term_show);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "show"), l_Lean_Parser_Term_show);
w = l___regBuiltinParser_Lean_Parser_Term_show(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_fun___elambda__1___closed__1 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__1);
l_Lean_Parser_Term_fun___elambda__1___closed__2 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__2);
l_Lean_Parser_Term_fun___elambda__1___closed__3 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__3);
l_Lean_Parser_Term_fun___elambda__1___closed__4 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__4);
l_Lean_Parser_Term_fun___elambda__1___closed__5 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__5);
l_Lean_Parser_Term_fun___elambda__1___closed__6 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__6);
l_Lean_Parser_Term_fun___elambda__1___closed__7 = _init_l_Lean_Parser_Term_fun___elambda__1___closed__7();
lean::mark_persistent(l_Lean_Parser_Term_fun___elambda__1___closed__7);
l_Lean_Parser_Term_fun = _init_l_Lean_Parser_Term_fun();
lean::mark_persistent(l_Lean_Parser_Term_fun);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "fun"), l_Lean_Parser_Term_fun);
w = l___regBuiltinParser_Lean_Parser_Term_fun(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_structInstField___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_structInstField = _init_l_Lean_Parser_Term_structInstField();
lean::mark_persistent(l_Lean_Parser_Term_structInstField);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "structInstField"), l_Lean_Parser_Term_structInstField);
l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_structInstSource___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_structInstSource = _init_l_Lean_Parser_Term_structInstSource();
lean::mark_persistent(l_Lean_Parser_Term_structInstSource);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "structInstSource"), l_Lean_Parser_Term_structInstSource);
l_Lean_Parser_Term_structInst___elambda__1___closed__1 = _init_l_Lean_Parser_Term_structInst___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_structInst___elambda__1___closed__1);
l_Lean_Parser_Term_structInst___elambda__1___closed__2 = _init_l_Lean_Parser_Term_structInst___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_structInst___elambda__1___closed__2);
l_Lean_Parser_Term_structInst___elambda__1___closed__3 = _init_l_Lean_Parser_Term_structInst___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_structInst___elambda__1___closed__3);
l_Lean_Parser_Term_structInst___elambda__1___closed__4 = _init_l_Lean_Parser_Term_structInst___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_structInst___elambda__1___closed__4);
l_Lean_Parser_Term_structInst___elambda__1___closed__5 = _init_l_Lean_Parser_Term_structInst___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_structInst___elambda__1___closed__5);
l_Lean_Parser_Term_structInst = _init_l_Lean_Parser_Term_structInst();
lean::mark_persistent(l_Lean_Parser_Term_structInst);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "structInst"), l_Lean_Parser_Term_structInst);
w = l___regBuiltinParser_Lean_Parser_Term_structInst(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_typeSpec___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_typeSpec = _init_l_Lean_Parser_Term_typeSpec();
lean::mark_persistent(l_Lean_Parser_Term_typeSpec);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "typeSpec"), l_Lean_Parser_Term_typeSpec);
l_Lean_Parser_Term_optType = _init_l_Lean_Parser_Term_optType();
lean::mark_persistent(l_Lean_Parser_Term_optType);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "optType"), l_Lean_Parser_Term_optType);
l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_subtype___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_subtype = _init_l_Lean_Parser_Term_subtype();
lean::mark_persistent(l_Lean_Parser_Term_subtype);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "subtype"), l_Lean_Parser_Term_subtype);
w = l___regBuiltinParser_Lean_Parser_Term_subtype(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_list___elambda__1___closed__1 = _init_l_Lean_Parser_Term_list___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_list___elambda__1___closed__1);
l_Lean_Parser_Term_list___elambda__1___closed__2 = _init_l_Lean_Parser_Term_list___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_list___elambda__1___closed__2);
l_Lean_Parser_Term_list___elambda__1___closed__3 = _init_l_Lean_Parser_Term_list___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_list___elambda__1___closed__3);
l_Lean_Parser_Term_list___elambda__1___closed__4 = _init_l_Lean_Parser_Term_list___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_list___elambda__1___closed__4);
l_Lean_Parser_Term_list___elambda__1___closed__5 = _init_l_Lean_Parser_Term_list___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_list___elambda__1___closed__5);
l_Lean_Parser_Term_list___elambda__1___closed__6 = _init_l_Lean_Parser_Term_list___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Term_list___elambda__1___closed__6);
l_Lean_Parser_Term_list = _init_l_Lean_Parser_Term_list();
lean::mark_persistent(l_Lean_Parser_Term_list);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "list"), l_Lean_Parser_Term_list);
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
l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_binderDefault___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_binderDefault = _init_l_Lean_Parser_Term_binderDefault();
lean::mark_persistent(l_Lean_Parser_Term_binderDefault);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "binderDefault"), l_Lean_Parser_Term_binderDefault);
l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_binderTactic___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_binderTactic = _init_l_Lean_Parser_Term_binderTactic();
lean::mark_persistent(l_Lean_Parser_Term_binderTactic);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "binderTactic"), l_Lean_Parser_Term_binderTactic);
l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1 = _init_l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___elambda__1___closed__1);
l_Lean_Parser_Term_explicitBinder___closed__1 = _init_l_Lean_Parser_Term_explicitBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__1);
l_Lean_Parser_Term_explicitBinder___closed__2 = _init_l_Lean_Parser_Term_explicitBinder___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__2);
l_Lean_Parser_Term_explicitBinder___closed__3 = _init_l_Lean_Parser_Term_explicitBinder___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_explicitBinder___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "explicitBinder"), 1, l_Lean_Parser_Term_explicitBinder___boxed);
l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1 = _init_l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1);
l_Lean_Parser_Term_implicitBinder___closed__1 = _init_l_Lean_Parser_Term_implicitBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__1);
l_Lean_Parser_Term_implicitBinder___closed__2 = _init_l_Lean_Parser_Term_implicitBinder___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_implicitBinder___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "implicitBinder"), 1, l_Lean_Parser_Term_implicitBinder___boxed);
l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_instBinder = _init_l_Lean_Parser_Term_instBinder();
lean::mark_persistent(l_Lean_Parser_Term_instBinder);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "instBinder"), l_Lean_Parser_Term_instBinder);
l_Lean_Parser_Term_bracktedBinder___closed__1 = _init_l_Lean_Parser_Term_bracktedBinder___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_bracktedBinder___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "bracktedBinder"), 1, l_Lean_Parser_Term_bracktedBinder___boxed);
l_Lean_Parser_Term_depArrow___elambda__1___closed__1 = _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_depArrow___elambda__1___closed__1);
l_Lean_Parser_Term_depArrow___elambda__1___closed__2 = _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_depArrow___elambda__1___closed__2);
l_Lean_Parser_Term_depArrow___elambda__1___closed__3 = _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_depArrow___elambda__1___closed__3);
l_Lean_Parser_Term_depArrow___elambda__1___closed__4 = _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_depArrow___elambda__1___closed__4);
l_Lean_Parser_Term_depArrow___elambda__1___closed__5 = _init_l_Lean_Parser_Term_depArrow___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_depArrow___elambda__1___closed__5);
l_Lean_Parser_Term_depArrow = _init_l_Lean_Parser_Term_depArrow();
lean::mark_persistent(l_Lean_Parser_Term_depArrow);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "depArrow"), l_Lean_Parser_Term_depArrow);
w = l___regBuiltinParser_Lean_Parser_Term_depArrow(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1 = _init_l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_simpleBinder___elambda__1___closed__1);
l_Lean_Parser_Term_simpleBinder = _init_l_Lean_Parser_Term_simpleBinder();
lean::mark_persistent(l_Lean_Parser_Term_simpleBinder);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "simpleBinder"), l_Lean_Parser_Term_simpleBinder);
l_Lean_Parser_Term_forall___elambda__1___closed__1 = _init_l_Lean_Parser_Term_forall___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_forall___elambda__1___closed__1);
l_Lean_Parser_Term_forall___elambda__1___closed__2 = _init_l_Lean_Parser_Term_forall___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_forall___elambda__1___closed__2);
l_Lean_Parser_Term_forall___elambda__1___closed__3 = _init_l_Lean_Parser_Term_forall___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_forall___elambda__1___closed__3);
l_Lean_Parser_Term_forall___elambda__1___closed__4 = _init_l_Lean_Parser_Term_forall___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_forall___elambda__1___closed__4);
l_Lean_Parser_Term_forall___elambda__1___closed__5 = _init_l_Lean_Parser_Term_forall___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_forall___elambda__1___closed__5);
l_Lean_Parser_Term_forall = _init_l_Lean_Parser_Term_forall();
lean::mark_persistent(l_Lean_Parser_Term_forall);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "forall"), l_Lean_Parser_Term_forall);
w = l___regBuiltinParser_Lean_Parser_Term_forall(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_equation___elambda__1___closed__1 = _init_l_Lean_Parser_Term_equation___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_equation___elambda__1___closed__1);
l_Lean_Parser_Term_equation___elambda__1___closed__2 = _init_l_Lean_Parser_Term_equation___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_equation___elambda__1___closed__2);
l_Lean_Parser_Term_equation___elambda__1___closed__3 = _init_l_Lean_Parser_Term_equation___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_equation___elambda__1___closed__3);
l_Lean_Parser_Term_equation___elambda__1___closed__4 = _init_l_Lean_Parser_Term_equation___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_equation___elambda__1___closed__4);
l_Lean_Parser_Term_equation___elambda__1___closed__5 = _init_l_Lean_Parser_Term_equation___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_equation___elambda__1___closed__5);
l_Lean_Parser_Term_equation = _init_l_Lean_Parser_Term_equation();
lean::mark_persistent(l_Lean_Parser_Term_equation);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "equation"), l_Lean_Parser_Term_equation);
l_Lean_Parser_Term_match___elambda__1___closed__1 = _init_l_Lean_Parser_Term_match___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_match___elambda__1___closed__1);
l_Lean_Parser_Term_match___elambda__1___closed__2 = _init_l_Lean_Parser_Term_match___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_match___elambda__1___closed__2);
l_Lean_Parser_Term_match___elambda__1___closed__3 = _init_l_Lean_Parser_Term_match___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_match___elambda__1___closed__3);
l_Lean_Parser_Term_match___elambda__1___closed__4 = _init_l_Lean_Parser_Term_match___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Term_match___elambda__1___closed__4);
l_Lean_Parser_Term_match___elambda__1___closed__5 = _init_l_Lean_Parser_Term_match___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Term_match___elambda__1___closed__5);
l_Lean_Parser_Term_match = _init_l_Lean_Parser_Term_match();
lean::mark_persistent(l_Lean_Parser_Term_match);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "match"), l_Lean_Parser_Term_match);
w = l___regBuiltinParser_Lean_Parser_Term_match(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__2);
l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_nomatch___elambda__1___rarg___closed__3);
l_Lean_Parser_Term_nomatch = _init_l_Lean_Parser_Term_nomatch();
lean::mark_persistent(l_Lean_Parser_Term_nomatch);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "nomatch"), l_Lean_Parser_Term_nomatch);
w = l___regBuiltinParser_Lean_Parser_Term_nomatch(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__1);
l_Lean_Parser_Term_namedArgument = _init_l_Lean_Parser_Term_namedArgument();
lean::mark_persistent(l_Lean_Parser_Term_namedArgument);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "namedArgument"), l_Lean_Parser_Term_namedArgument);
l_Lean_Parser_Term_app___elambda__1___closed__1 = _init_l_Lean_Parser_Term_app___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_app___elambda__1___closed__1);
l_Lean_Parser_Term_app = _init_l_Lean_Parser_Term_app();
lean::mark_persistent(l_Lean_Parser_Term_app);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "app"), l_Lean_Parser_Term_app);
w = l___regBuiltinParser_Lean_Parser_Term_app(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_proj___elambda__1___closed__1 = _init_l_Lean_Parser_Term_proj___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_proj___elambda__1___closed__1);
l_Lean_Parser_Term_proj___elambda__1___closed__2 = _init_l_Lean_Parser_Term_proj___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_proj___elambda__1___closed__2);
l_Lean_Parser_Term_proj___elambda__1___closed__3 = _init_l_Lean_Parser_Term_proj___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Term_proj___elambda__1___closed__3);
l_Lean_Parser_Term_proj = _init_l_Lean_Parser_Term_proj();
lean::mark_persistent(l_Lean_Parser_Term_proj);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "proj"), l_Lean_Parser_Term_proj);
w = l___regBuiltinParser_Lean_Parser_Term_proj(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_arrow___elambda__1___closed__1 = _init_l_Lean_Parser_Term_arrow___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_arrow___elambda__1___closed__1);
l_Lean_Parser_Term_arrow = _init_l_Lean_Parser_Term_arrow();
lean::mark_persistent(l_Lean_Parser_Term_arrow);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "arrow"), l_Lean_Parser_Term_arrow);
w = l___regBuiltinParser_Lean_Parser_Term_arrow(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_array___elambda__1___closed__1 = _init_l_Lean_Parser_Term_array___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_array___elambda__1___closed__1);
l_Lean_Parser_Term_array___elambda__1___closed__2 = _init_l_Lean_Parser_Term_array___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Term_array___elambda__1___closed__2);
l_Lean_Parser_Term_array = _init_l_Lean_Parser_Term_array();
lean::mark_persistent(l_Lean_Parser_Term_array);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "array"), l_Lean_Parser_Term_array);
w = l___regBuiltinParser_Lean_Parser_Term_array(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_fcomp___elambda__1___closed__1 = _init_l_Lean_Parser_Term_fcomp___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_fcomp___elambda__1___closed__1);
l_Lean_Parser_Term_fcomp = _init_l_Lean_Parser_Term_fcomp();
lean::mark_persistent(l_Lean_Parser_Term_fcomp);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "fcomp"), l_Lean_Parser_Term_fcomp);
w = l___regBuiltinParser_Lean_Parser_Term_fcomp(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_add___elambda__1___closed__1 = _init_l_Lean_Parser_Term_add___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_add___elambda__1___closed__1);
l_Lean_Parser_Term_add = _init_l_Lean_Parser_Term_add();
lean::mark_persistent(l_Lean_Parser_Term_add);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "add"), l_Lean_Parser_Term_add);
w = l___regBuiltinParser_Lean_Parser_Term_add(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_sub___elambda__1___closed__1 = _init_l_Lean_Parser_Term_sub___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_sub___elambda__1___closed__1);
l_Lean_Parser_Term_sub = _init_l_Lean_Parser_Term_sub();
lean::mark_persistent(l_Lean_Parser_Term_sub);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "sub"), l_Lean_Parser_Term_sub);
w = l___regBuiltinParser_Lean_Parser_Term_sub(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_mul___elambda__1___closed__1 = _init_l_Lean_Parser_Term_mul___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_mul___elambda__1___closed__1);
l_Lean_Parser_Term_mul = _init_l_Lean_Parser_Term_mul();
lean::mark_persistent(l_Lean_Parser_Term_mul);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "mul"), l_Lean_Parser_Term_mul);
w = l___regBuiltinParser_Lean_Parser_Term_mul(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_div___elambda__1___closed__1 = _init_l_Lean_Parser_Term_div___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_div___elambda__1___closed__1);
l_Lean_Parser_Term_div = _init_l_Lean_Parser_Term_div();
lean::mark_persistent(l_Lean_Parser_Term_div);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "div"), l_Lean_Parser_Term_div);
w = l___regBuiltinParser_Lean_Parser_Term_div(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_mod___elambda__1___closed__1 = _init_l_Lean_Parser_Term_mod___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_mod___elambda__1___closed__1);
l_Lean_Parser_Term_mod = _init_l_Lean_Parser_Term_mod();
lean::mark_persistent(l_Lean_Parser_Term_mod);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "mod"), l_Lean_Parser_Term_mod);
w = l___regBuiltinParser_Lean_Parser_Term_mod(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_modN___elambda__1___closed__1 = _init_l_Lean_Parser_Term_modN___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_modN___elambda__1___closed__1);
l_Lean_Parser_Term_modN = _init_l_Lean_Parser_Term_modN();
lean::mark_persistent(l_Lean_Parser_Term_modN);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "modN"), l_Lean_Parser_Term_modN);
w = l___regBuiltinParser_Lean_Parser_Term_modN(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_le___elambda__1___closed__1 = _init_l_Lean_Parser_Term_le___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_le___elambda__1___closed__1);
l_Lean_Parser_Term_le = _init_l_Lean_Parser_Term_le();
lean::mark_persistent(l_Lean_Parser_Term_le);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "le"), l_Lean_Parser_Term_le);
w = l___regBuiltinParser_Lean_Parser_Term_le(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_ge___elambda__1___closed__1 = _init_l_Lean_Parser_Term_ge___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_ge___elambda__1___closed__1);
l_Lean_Parser_Term_ge = _init_l_Lean_Parser_Term_ge();
lean::mark_persistent(l_Lean_Parser_Term_ge);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "ge"), l_Lean_Parser_Term_ge);
w = l___regBuiltinParser_Lean_Parser_Term_ge(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_lt___elambda__1___closed__1 = _init_l_Lean_Parser_Term_lt___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_lt___elambda__1___closed__1);
l_Lean_Parser_Term_lt = _init_l_Lean_Parser_Term_lt();
lean::mark_persistent(l_Lean_Parser_Term_lt);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "lt"), l_Lean_Parser_Term_lt);
w = l___regBuiltinParser_Lean_Parser_Term_lt(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_gt___elambda__1___closed__1 = _init_l_Lean_Parser_Term_gt___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_gt___elambda__1___closed__1);
l_Lean_Parser_Term_gt = _init_l_Lean_Parser_Term_gt();
lean::mark_persistent(l_Lean_Parser_Term_gt);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "gt"), l_Lean_Parser_Term_gt);
w = l___regBuiltinParser_Lean_Parser_Term_gt(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_eq___elambda__1___closed__1 = _init_l_Lean_Parser_Term_eq___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_eq___elambda__1___closed__1);
l_Lean_Parser_Term_eq = _init_l_Lean_Parser_Term_eq();
lean::mark_persistent(l_Lean_Parser_Term_eq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "eq"), l_Lean_Parser_Term_eq);
w = l___regBuiltinParser_Lean_Parser_Term_eq(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_beq___elambda__1___closed__1 = _init_l_Lean_Parser_Term_beq___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_beq___elambda__1___closed__1);
l_Lean_Parser_Term_beq = _init_l_Lean_Parser_Term_beq();
lean::mark_persistent(l_Lean_Parser_Term_beq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "beq"), l_Lean_Parser_Term_beq);
w = l___regBuiltinParser_Lean_Parser_Term_beq(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_and___elambda__1___closed__1 = _init_l_Lean_Parser_Term_and___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_and___elambda__1___closed__1);
l_Lean_Parser_Term_and = _init_l_Lean_Parser_Term_and();
lean::mark_persistent(l_Lean_Parser_Term_and);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "and"), l_Lean_Parser_Term_and);
w = l___regBuiltinParser_Lean_Parser_Term_and(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_or___elambda__1___closed__1 = _init_l_Lean_Parser_Term_or___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_or___elambda__1___closed__1);
l_Lean_Parser_Term_or = _init_l_Lean_Parser_Term_or();
lean::mark_persistent(l_Lean_Parser_Term_or);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "or"), l_Lean_Parser_Term_or);
w = l___regBuiltinParser_Lean_Parser_Term_or(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Term_iff___elambda__1___closed__1 = _init_l_Lean_Parser_Term_iff___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_iff___elambda__1___closed__1);
l_Lean_Parser_Term_iff = _init_l_Lean_Parser_Term_iff();
lean::mark_persistent(l_Lean_Parser_Term_iff);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Term"), "iff"), l_Lean_Parser_Term_iff);
w = l___regBuiltinParser_Lean_Parser_Term_iff(w);
if (io_result_is_error(w)) return w;
return w;
}
