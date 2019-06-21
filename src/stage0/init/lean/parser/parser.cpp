// Lean compiler output
// Module: init.lean.parser.parser
// Imports: init.lean.position init.lean.syntax init.lean.toexpr init.lean.environment init.lean.attributes init.lean.parser.trie init.lean.parser.identifier init.lean.compiler.initattr
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
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_Parser_checkLeadingFn___closed__1;
obj* l_Lean_Parser_runParser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn(obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___closed__1;
obj* l_Lean_Parser_regBuiltinTermParserAttr(obj*);
obj* l_Lean_Parser_mkAtomicInfo___closed__1;
obj* l_Lean_Parser_testParser___elambda__1___closed__1;
obj* l_Lean_Parser_unicodeSymbolFnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParser(obj*);
obj* l_Lean_Parser_numberFnAux___closed__1;
obj* l_Lean_Parser_strLitFnAux(obj*, obj*, obj*);
obj* l_Lean_Parser_sepByInfo___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_orelseFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_finishCommentBlock(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_strLitFn___boxed(obj*, obj*);
uint8 l_Lean_Parser_isIdCont___main(obj*, obj*);
obj* l_Lean_Parser_ParserState_shrinkStack(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_anyOfFn___main(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_declareLeadingBuiltinParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_addBuiltinLeadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1(uint8, obj*, obj*, uint8);
obj* l_Lean_Parser_longestMatchFnAux(uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited___rarg(obj*);
obj* l_Lean_Parser_andthenFn___boxed(obj*);
obj* l_Lean_Parser_epsilonInfo___elambda__1(obj*);
obj* l_Lean_FileMap_toPosition___main(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_Parser_tryFn___main(uint8);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_TokenConfig_beq___boxed(obj*, obj*);
obj* l_Lean_Parser_whitespace___main(obj*, obj*);
uint8 l_Lean_isIdRest(uint32);
obj* l_Lean_Parser_sepBy1Fn___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_6__mkResult(obj*, obj*);
obj* l_Lean_Parser_numLit___boxed(obj*);
extern obj* l_Lean_stxInh;
obj* l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
obj* l_Lean_Parser_orelseFn(uint8);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main(uint8, obj*, obj*, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_builtinCommandParsingTable;
uint8 l_Lean_isIdEndEscape(uint32);
obj* l_Lean_Parser_termParser___elambda__1___closed__1;
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_termParser___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_anyOfFn___main___closed__1;
obj* l_Lean_Parser_commandParser___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinCommandParserAttr___closed__1;
obj* l_Lean_Parser_anyOfFn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchMkResult(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_hasError___boxed(obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_numLit(uint8);
obj* l_Lean_Parser_decimalNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_sepByFn___main(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_leadingParser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
obj* l_Lean_Parser_tryFn___main___boxed(obj*);
obj* l_Lean_Parser_currLbp___closed__1;
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_mkTokenAndFixPos___closed__1;
extern obj* l_Lean_registerTagAttribute___lambda__5___closed__1;
obj* l_Lean_Parser_sepBy1Info___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_runBuiltinParser___rarg___boxed(obj*);
obj* l_Lean_Parser_takeUntilFn___main(obj*, obj*, obj*);
obj* l_Lean_Parser_hexDigitFn___main___boxed(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3___boxed(obj*, obj*);
obj* l_Lean_Parser_strLitFnAux___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_runBuiltinParser___rarg(obj*);
obj* l_Lean_Parser_many1___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_mkParserContext(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_runBuiltinParserUnsafe___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_stackSize(obj*);
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
obj* l_Lean_Parser_hexDigitFn___main(obj*, obj*);
obj* l_Lean_Parser_ParserState_toErrorMsg___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux(uint8, obj*, obj*, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_builtinTermParsingTable;
obj* l_Lean_Parser_mkNodeToken___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_keepLatest(obj*, obj*);
obj* l_Lean_Parser_initCacheForInput(obj*);
obj* l_Lean_Parser_sepBy1Fn___main(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawFn___boxed(obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Parser_tryFn___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(obj*, obj*);
obj* l_Lean_Parser_ParserState_toErrorMsg___closed__2;
obj* l_Lean_Parser_hexDigitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_string2basic___boxed(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_insert___rarg(obj*, obj*, obj*);
uint8 l_List_isEmpty___main___rarg(obj*);
obj* l___private_init_lean_parser_parser_4__tokenFnAux___main(obj*, obj*);
obj* l_Lean_Parser_rawFn___main___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTestParserAttr___closed__2;
obj* l_Lean_Parser_Parser_inhabited(uint8);
obj* l_Lean_Parser_unicodeSymbolFn(uint8);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4;
uint8 l_Lean_Parser_TokenConfig_beq___main(obj*, obj*);
obj* l_Lean_Parser_ParserState_mergeErrors___boxed(obj*, obj*, obj*);
uint8 l_Lean_Syntax_isOfKind___main(obj*, obj*);
obj* l_Lean_Parser_addBuiltinLeadingParser___closed__1;
obj* l_Lean_Parser_longestMatchFn___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(obj*, obj*, obj*);
obj* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parser_3__isToken___boxed(obj*);
obj* l_Lean_Parser_strLitFn___rarg___closed__1;
obj* l_Lean_Parser_symbolFnAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_identFnAux___main___closed__1;
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_declareTrailingBuiltinParser___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn(obj*, obj*, obj*);
obj* l_Lean_Parser_quotedCharFn___main___boxed(obj*, obj*);
obj* l_Lean_Parser_optional___boxed(obj*, obj*);
obj* l_Lean_Parser_isIdCont___boxed(obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_checkLeadingFn(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_quotedCharFn(obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___closed__1;
obj* l_Lean_Parser_termParser___elambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn___main(uint8, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_Parser_longestMatchFn(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___boxed(obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_currLbp(obj*, obj*);
obj* l_Lean_Parser_strLitFnAux___main___boxed(obj*, obj*, obj*);
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_Lean_Parser_unicodeSymbol___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4(obj*, obj*, obj*);
obj* l_Lean_Parser_mkAtomicInfo(obj*);
obj* l_Lean_Parser_satisfyFn___main(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(obj*);
obj* l_Lean_Parser_mkParserState(obj*);
obj* l_Lean_Parser_nodeFn___boxed(obj*);
obj* l_Lean_Parser_hexNumberFn___closed__1;
obj* l_Lean_Parser_addBuiltinTrailingParser___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_leadingParser___closed__1;
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5;
obj* l_Lean_Parser_longestMatchFn___main___closed__1;
obj* l_Lean_Parser_nodeFn___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_node___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_optional(uint8, obj*);
obj* l_Lean_Parser_whitespace___main___boxed(obj*, obj*);
obj* l_Lean_Parser_anyOfFn___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mergeErrors(obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___closed__2;
obj* l_Lean_Parser_indexed___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_FirstTokens_seq___boxed(obj*, obj*);
obj* l_Lean_Parser_strLitFn(uint8, obj*);
obj* l_Lean_Parser_ParserState_replaceLongest(obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3___boxed(obj*, obj*);
obj* l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(obj*);
obj* l_Lean_Parser_trailingLoop___main(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___boxed(obj*);
uint8 l___private_init_lean_parser_parser_3__isToken___rarg(obj*, obj*);
obj* l_Lean_Parser_optionalFn___boxed(obj*);
obj* l_Lean_Parser_declareTrailingBuiltinParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkParserState___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_quotedCharFn___boxed(obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*);
obj* l_Lean_Parser_declareBuiltinParser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken___closed__1;
obj* l_Lean_Parser_trailingLoop___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_initAttr;
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(obj*);
obj* l_Lean_Parser_finishCommentBlock___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_Inhabited(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Parser_mkNodeToken(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_node(uint8, obj*, obj*);
obj* l_Lean_Parser_numLitKind;
obj* l_Lean_Parser_rawFn___main(uint8);
obj* l_Lean_Parser_andthen___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_nodeFn___main___boxed(obj*);
obj* l_Lean_Parser_ParserState_mkEOIError___closed__1;
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___main___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_restore___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1(obj*, obj*, obj*);
obj* l_Array_extract___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_next___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__2;
obj* l___private_init_lean_parser_parser_2__rawAux___main(uint8);
obj* l_Lean_Parser_binNumberFn___closed__1;
obj* l___private_init_lean_parser_parser_2__rawAux(uint8);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(obj*, obj*);
obj* l_Lean_Parser_ParserState_mergeErrors___closed__1;
uint8 l_Lean_isIdBeginEscape(uint32);
obj* l_Lean_Parser_mkEmptySubstringAt(obj*, obj*);
obj* l_Lean_Parser_binNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_TokenConfig_HasBeq;
obj* l_Lean_Parser_manyAux___main___closed__1;
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_testParser___elambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l_Lean_Parser_FirstTokens_merge___main(obj*, obj*);
obj* l_Lean_Parser_ParserState_shrinkStack___boxed(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___lambda__1(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhile1Fn(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTestParserAttr(obj*);
obj* l_Lean_Parser_manyFn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol(uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_runParser___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_UInt32_decLe(uint32, uint32);
obj* l_Lean_Parser_optionalFn(uint8);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_Lean_Parser_sepBy(uint8, obj*, obj*, uint8);
obj* l_Lean_Parser_FirstTokens_seq(obj*, obj*);
obj* l_Lean_Parser_andthenFn(uint8);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_sepByFn___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Parser_checkLeadingFn___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_orelseFn___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___boxed(obj*);
obj* l_Lean_Parser_strLitFnAux___main(obj*, obj*, obj*);
uint8 l_Lean_Parser_isIdCont(obj*, obj*);
uint8 l_Lean_Syntax_isIdent___main(obj*);
obj* l_Lean_Parser_ident(uint8);
obj* l_Lean_Parser_tokenFn(obj*, obj*);
obj* l_Lean_Parser_currLbp___closed__2;
extern obj* l_Lean_registerTagAttribute___closed__6;
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_tryFn___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinCommandParserAttr(obj*);
obj* l_Lean_Parser_ParserFn_inhabited___rarg___boxed(obj*);
obj* l_Lean_Parser_ParserState_toErrorMsg___closed__1;
uint8 l_Lean_Syntax_isMissing___main(obj*);
obj* l_Lean_Parser_sepByFn(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace___boxed(obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_declareBuiltinParser___closed__2;
obj* l_Lean_Parser_orelseFn___main___boxed(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(obj*, obj*);
obj* l_Lean_Parser_testParser(obj*);
obj* l_Lean_nameToExprAux___main(obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_mkTokenAndFixPos___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyFn(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_commandParser___elambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_strLit(uint8);
obj* l_Lean_Parser_orelseFn___main(uint8);
obj* l_Lean_Parser_rawFn___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_add_and_compile(obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFnAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_binNumberFn___boxed(obj*, obj*, obj*);
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_many___boxed(obj*, obj*);
obj* l_Lean_Parser_hexNumberFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_keepPrevError(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_strLitFn___rarg(obj*, obj*);
obj* l_Lean_Parser_addBuiltinTrailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj*, obj*, obj*);
extern obj* l_Lean_choiceKind;
obj* l_Lean_Parser_unicodeSymbolFnAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6(obj*);
obj* l_Lean_Parser_runBuiltinParser___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_octalNumberFn___closed__1;
obj* l_Lean_Parser_rawFn(uint8);
obj* l_Lean_Parser_declareBuiltinParser___closed__1;
obj* l_Lean_Parser_tryFn___boxed(obj*);
obj* l_Lean_Parser_identFnAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_setPos(obj*, obj*);
obj* l_Lean_Parser_numberFnAux___boxed(obj*, obj*);
obj* l_Lean_Parser_prattParser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol___boxed(obj*, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_empty(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Parser_satisfyFn___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_pushLeadingFn(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ident___closed__1;
obj* l_Lean_Parser_addBuiltinLeadingParser___closed__2;
obj* l_Lean_Parser_Parser_inhabited___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinCommandParserAttr___closed__2;
obj* l_Lean_Parser_TokenMap_insert(obj*);
obj* l_Lean_Parser_takeUntilFn___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1(obj*, obj*, obj*);
extern obj* l_unsafeIO___rarg___closed__1;
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
obj* l_Lean_Parser_many1(uint8, obj*);
obj* l_Lean_Parser_trailingLoop___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken___closed__2;
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Lean_Parser_longestMatchFn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhile1Fn___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_hexDigitFn___main___closed__1;
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_Parser_indexed___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn_u2081___boxed(obj*);
obj* l_Lean_Parser_string2basic(uint8, obj*);
obj* l_Lean_Parser_many(uint8, obj*);
obj* l_Lean_Parser_finishCommentBlock___main(obj*, obj*, obj*);
uint8 l_Lean_Parser_TokenConfig_beq(obj*, obj*);
obj* l___private_init_lean_parser_parser_4__tokenFnAux(obj*, obj*);
obj* l_Lean_mkCApp(obj*, obj*);
obj* l_Lean_Parser_numLitFn___rarg(obj*, obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
extern obj* l_Lean_registerTagAttribute___lambda__5___closed__2;
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l_Lean_Parser_commandParser(obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_runBuiltinParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_octalNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_FirstTokens_seq___main___boxed(obj*, obj*);
obj* l_Lean_Parser_nodeFn___main(uint8);
obj* l_Lean_Parser_ParserState_popSyntax(obj*);
obj* l_Lean_Parser_try___boxed(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3___boxed(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_try(uint8, obj*);
obj* l_Lean_Parser_numLit___closed__1;
obj* l_Lean_Parser_ParserState_keepNewError(obj*, obj*);
obj* l_Lean_Parser_identFnAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_initCacheForInput___boxed(obj*);
obj* l_Lean_Parser_finishCommentBlock___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(obj*, obj*);
obj* l_Lean_Parser_FirstTokens_merge(obj*, obj*);
obj* l_Lean_Parser_nodeFn(uint8);
obj* l_Lean_Parser_octalNumberFn___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_Lean_Parser_longestMatchStep(uint8);
obj* l_Lean_Parser_checkLeading(obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
obj* l_Lean_Parser_optionalFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
obj* l_Lean_Parser_TokenConfig_beq___main___boxed(obj*, obj*);
obj* l_Lean_Parser_sepBy1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_regBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_unicodeSymbolFn___boxed(obj*);
obj* l_Lean_Parser_numLitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_andthenAux(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_pop(obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_Parser_identFnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_declareBuiltinParser___closed__3;
obj* l_Lean_ParametricAttribute_setParam___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_ConstantInfo_type(obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(obj*, obj*);
obj* l_Lean_Parser_ParserState_mkEOIError(obj*);
obj* l_Lean_Parser_longestMatchFn_u2081___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn_u2081(uint8);
obj* l_Lean_Parser_ParserState_setCache(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(obj*);
obj* l_Lean_Parser_ParserState_mkError(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7(obj*);
obj* l_Lean_Parser_quotedCharFn___main(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Lean_Parser_declareLeadingBuiltinParser___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_decimalNumberFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_andthen(uint8, obj*, obj*);
obj* l_Lean_Parser_satisfySymbolFn(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_5__updateCache(obj*, obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_Lean_Parser_ParserState_keepNewError___boxed(obj*, obj*);
obj* l_Lean_Parser_ParserState_keepPrevError___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux(uint8, obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_trailingParser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_peekToken(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_prattParser(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_3__isToken___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6;
obj* l_Lean_Parser_strLit___closed__1;
obj* l_Lean_Parser_trailingParser___closed__1;
obj* l_Lean_Parser_unicodeSymbolFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_identFn___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1(obj*, obj*, obj*);
extern obj* l_Lean_registerTagAttribute___lambda__5___closed__3;
obj* l_Lean_Parser_mkIdResult(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkIdResult___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_numberFnAux(obj*, obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
uint8 l_Lean_Parser_ParserState_hasError(obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_indexed(obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(obj*, obj*, obj*, obj*, obj*, uint8, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_registerTagAttribute___closed__5;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1___boxed(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Lean_Parser_nodeFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkAtomicInfo___elambda__1(obj*);
obj* l_Lean_Parser_sepBy___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_next(obj*, obj*, obj*);
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
obj* l_Lean_Parser_strLit___boxed(obj*);
obj* l_Lean_Parser_orelseFn___boxed(obj*);
obj* l_Lean_Parser_mkBuiltinParsingTablesRef___closed__1;
namespace lean {
obj* string_utf8_byte_size(obj*);
}
obj* l_Lean_Parser_builtinTestParsingTable;
obj* l_Lean_Parser_ident___boxed(obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_rawFn___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_7__updateTokens(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_stackSize___boxed(obj*);
obj* l_Lean_Parser_identFn(uint8, obj*);
obj* l_Lean_Parser_identFnAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_quotedCharFn___main___closed__1;
obj* l_Lean_Parser_andthenInfo___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkErrorAt(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolInfo(obj*, obj*, obj*);
obj* l_Lean_Parser_rawFn___main___boxed(obj*);
obj* l_Lean_Parser_TokenMap_HasEmptyc(obj*);
obj* l_Lean_Parser_longestMatchFnAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_pushLeading;
obj* l_Lean_Parser_tryFn(uint8);
obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_ParserState_toErrorMsg(obj*, obj*);
obj* l_Lean_Parser_symbolFn(uint8);
obj* l_Lean_Parser_identFn___rarg___closed__1;
obj* l_Lean_Parser_hexNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_runBuiltinParserUnsafe___closed__1;
obj* l_Lean_Parser_orelse(uint8, obj*, obj*);
obj* l_Lean_Parser_satisfyFn(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_orelse___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken___closed__3;
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
obj* l_Lean_Parser_FirstTokens_seq___main(obj*, obj*);
obj* l_Lean_Parser_declareBuiltinParser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1;
obj* l_Lean_Parser_hexDigitFn(obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken(obj*, obj*, obj*);
obj* l_Lean_Parser_trailingParser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
uint8 l_Lean_isIdFirst(uint32);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(obj*);
obj* l_Lean_Parser_mkTokenAndFixPos(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolInfo___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_leadingParser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol(uint8, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_rawFn___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_keepLatest___boxed(obj*, obj*);
obj* l_Lean_Parser_numLitFn(uint8, obj*);
obj* l_Lean_FileMap_ofString(obj*);
obj* l_Lean_Parser_isIdCont___main___boxed(obj*, obj*);
obj* l_Lean_Parser_regBuiltinTestParserAttr___closed__1;
obj* l_Lean_Parser_strLitKind;
obj* l_Lean_Parser_sepByFn___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___main___boxed(obj*);
obj* l_Lean_Parser_longestMatchStep___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(obj*, obj*);
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_commandParser___elambda__1___closed__1;
obj* l_Lean_Parser_trailingLoop(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkLongestNodeAlt(obj*, obj*);
obj* l_Lean_Parser_anyOfFn(uint8, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchStep___boxed(obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_3__isToken(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_replaceLongest___boxed(obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepByInfo(obj*, obj*);
obj* l_Lean_Parser_longestMatchFnAux___main(uint8, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_orelseInfo___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited(uint8, obj*, obj*);
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* l_Lean_Parser_testParser___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_addBuiltinLeadingParser___boxed(obj*, obj*, obj*, obj*);
obj* _init_l_Lean_Parser_maxPrec() {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(1024u);
return x_1;
}
}
uint8 l_Lean_Parser_TokenConfig_beq___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::string_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
}
else
{
if (lean::obj_tag(x_6) == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_4, 0);
x_13 = lean::cnstr_get(x_6, 0);
x_14 = lean::nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
}
}
}
}
obj* l_Lean_Parser_TokenConfig_beq___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Parser_TokenConfig_beq___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_Parser_TokenConfig_beq(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Parser_TokenConfig_beq___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_TokenConfig_beq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Parser_TokenConfig_beq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_TokenConfig_HasBeq() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_TokenConfig_beq___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_initCacheForInput(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_utf8_byte_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_2, x_3);
lean::dec(x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_6);
return x_7;
}
}
obj* l_Lean_Parser_initCacheForInput___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_Parser_ParserState_hasError(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 3);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_Lean_Parser_ParserState_hasError___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Parser_ParserState_hasError(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_stackSize(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::array_get_size(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_stackSize___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserState_stackSize(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserState_restore(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 3);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_1, 1);
lean::dec(x_7);
x_8 = l_Array_shrink___main___rarg(x_5, x_2);
x_9 = lean::box(0);
lean::cnstr_set(x_1, 3, x_9);
lean::cnstr_set(x_1, 1, x_3);
lean::cnstr_set(x_1, 0, x_8);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_12 = l_Array_shrink___main___rarg(x_10, x_2);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_3);
lean::cnstr_set(x_14, 2, x_11);
lean::cnstr_set(x_14, 3, x_13);
return x_14;
}
}
}
obj* l_Lean_Parser_ParserState_restore___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParserState_restore(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_ParserState_setPos(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_6);
lean::cnstr_set(x_8, 3, x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_ParserState_setCache(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 2);
lean::dec(x_4);
lean::cnstr_set(x_1, 2, x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 2, x_2);
lean::cnstr_set(x_8, 3, x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_ParserState_pushSyntax(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::array_push(x_4, x_2);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_10 = lean::array_push(x_6, x_2);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_ParserState_popSyntax(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::array_pop(x_3);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_9 = lean::array_pop(x_5);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set(x_10, 2, x_7);
lean::cnstr_set(x_10, 3, x_8);
return x_10;
}
}
}
obj* l_Lean_Parser_ParserState_shrinkStack(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = l_Array_shrink___main___rarg(x_4, x_2);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_10 = l_Array_shrink___main___rarg(x_6, x_2);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_ParserState_shrinkStack___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParserState_shrinkStack(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_next(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 1);
lean::dec(x_5);
x_6 = lean::string_utf8_next(x_2, x_3);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::string_utf8_next(x_2, x_3);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_ParserState_next___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParserState_next(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_ParserState_toErrorMsg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(":");
return x_1;
}
}
obj* _init_l_Lean_Parser_ParserState_toErrorMsg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" ");
return x_1;
}
}
obj* l_Lean_Parser_ParserState_toErrorMsg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_String_splitAux___main___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
x_8 = l_Lean_FileMap_toPosition___main(x_6, x_7);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
lean::dec(x_1);
x_10 = l_Lean_Parser_ParserState_toErrorMsg___closed__1;
x_11 = lean::string_append(x_9, x_10);
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
x_13 = l_Nat_repr(x_12);
x_14 = lean::string_append(x_11, x_13);
lean::dec(x_13);
x_15 = lean::string_append(x_14, x_10);
x_16 = lean::cnstr_get(x_8, 1);
lean::inc(x_16);
lean::dec(x_8);
x_17 = l_Nat_repr(x_16);
x_18 = lean::string_append(x_15, x_17);
lean::dec(x_17);
x_19 = l_Lean_Parser_ParserState_toErrorMsg___closed__2;
x_20 = lean::string_append(x_18, x_19);
x_21 = lean::string_append(x_20, x_5);
return x_21;
}
}
}
obj* l_Lean_Parser_ParserState_toErrorMsg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParserState_toErrorMsg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_mkNode(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_46; 
x_46 = 1;
x_8 = x_46;
goto block_45;
}
else
{
uint8 x_47; 
x_47 = 0;
x_8 = x_47;
goto block_45;
}
block_45:
{
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::array_get_size(x_4);
x_10 = lean::nat_dec_eq(x_9, x_3);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_1);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_1, 3);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_1, 2);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_1, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_1, 0);
lean::dec(x_15);
lean::inc(x_3);
x_16 = l_Array_extract___rarg(x_4, x_3, x_9);
lean::dec(x_9);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_18, 0, x_2);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Array_shrink___main___rarg(x_4, x_3);
lean::dec(x_3);
x_20 = lean::array_push(x_19, x_18);
lean::cnstr_set(x_1, 0, x_20);
return x_1;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
lean::inc(x_3);
x_21 = l_Array_extract___rarg(x_4, x_3, x_9);
lean::dec(x_9);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_Array_shrink___main___rarg(x_4, x_3);
lean::dec(x_3);
x_25 = lean::array_push(x_24, x_23);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_5);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_7);
return x_26;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_1;
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_28 = lean::cnstr_get(x_1, 3);
lean::dec(x_28);
x_29 = lean::cnstr_get(x_1, 2);
lean::dec(x_29);
x_30 = lean::cnstr_get(x_1, 1);
lean::dec(x_30);
x_31 = lean::cnstr_get(x_1, 0);
lean::dec(x_31);
x_32 = lean::array_get_size(x_4);
lean::inc(x_3);
x_33 = l_Array_extract___rarg(x_4, x_3, x_32);
lean::dec(x_32);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_Array_shrink___main___rarg(x_4, x_3);
lean::dec(x_3);
x_37 = lean::array_push(x_36, x_35);
lean::cnstr_set(x_1, 0, x_37);
return x_1;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_1);
x_38 = lean::array_get_size(x_4);
lean::inc(x_3);
x_39 = l_Array_extract___rarg(x_4, x_3, x_38);
lean::dec(x_38);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_39);
lean::cnstr_set(x_41, 2, x_40);
x_42 = l_Array_shrink___main___rarg(x_4, x_3);
lean::dec(x_3);
x_43 = lean::array_push(x_42, x_41);
x_44 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_5);
lean::cnstr_set(x_44, 2, x_6);
lean::cnstr_set(x_44, 3, x_7);
return x_44;
}
}
}
}
}
obj* l_Lean_Parser_ParserState_mkError(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 3);
lean::dec(x_4);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_1, 3, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_2);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_8);
lean::cnstr_set(x_10, 3, x_9);
return x_10;
}
}
}
obj* _init_l_Lean_Parser_ParserState_mkEOIError___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("end of input");
return x_1;
}
}
obj* l_Lean_Parser_ParserState_mkEOIError(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_3 = l_Lean_Parser_ParserState_mkError(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_mkErrorAt(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 3);
lean::dec(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::dec(x_6);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_1, 3, x_7);
lean::cnstr_set(x_1, 1, x_3);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_9);
lean::cnstr_set(x_11, 3, x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_ParserFn_inhabited___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Parser_ParserFn_inhabited(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParserFn_inhabited___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_Lean_Parser_ParserFn_inhabited___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserFn_inhabited___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserFn_inhabited___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_Parser_ParserFn_inhabited(x_4, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_FirstTokens_merge___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
return x_2;
}
default: 
{
lean::dec(x_2);
return x_1;
}
}
}
default: 
{
switch (lean::obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean::dec(x_1);
return x_2;
}
default: 
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = l_List_append___rarg(x_3, x_5);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = l_List_append___rarg(x_3, x_7);
x_9 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
}
}
}
obj* l_Lean_Parser_FirstTokens_merge(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_FirstTokens_merge___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_FirstTokens_seq___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Lean_Parser_FirstTokens_seq___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_FirstTokens_seq___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_FirstTokens_seq(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_FirstTokens_seq___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_FirstTokens_seq___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_FirstTokens_seq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Parser_inhabited___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::inc(x_3);
return x_3;
}
}
obj* _init_l_Lean_Parser_Parser_inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_lift___rarg___lambda__1), 1, 0);
x_2 = lean::box(1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Parser_inhabited___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parser_inhabited___lambda__1___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_Parser_inhabited(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_Parser_inhabited___closed__2;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Parser_inhabited___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Parser_inhabited___lambda__1(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Parser_inhabited___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_Parser_inhabited(x_2);
return x_3;
}
}
obj* l_Lean_Parser_epsilonInfo___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_epsilonInfo() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_epsilonInfo___elambda__1), 1, 0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_pushLeadingFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
return x_4;
}
}
obj* l_Lean_Parser_pushLeadingFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_pushLeadingFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_pushLeading() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_checkLeadingFn___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid leading token");
return x_1;
}
}
obj* l_Lean_Parser_checkLeadingFn(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::apply_1(x_1, x_2);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_checkLeadingFn___closed__1;
x_8 = l_Lean_Parser_ParserState_mkError(x_4, x_7);
return x_8;
}
else
{
return x_4;
}
}
}
obj* l_Lean_Parser_checkLeadingFn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_checkLeadingFn(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_checkLeading(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_checkLeadingFn___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_andthenAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
x_5 = lean::apply_2(x_1, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = lean::apply_2(x_2, x_3, x_5);
return x_7;
}
else
{
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
}
obj* l_Lean_Parser_andthenFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_4);
lean::inc(x_3);
x_6 = lean::apply_3(x_1, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::apply_3(x_2, x_3, x_4, x_6);
return x_8;
}
else
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
}
obj* l_Lean_Parser_andthenFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_andthenFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_andthenFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_andthenInfo___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::apply_1(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::apply_1(x_10, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_andthenInfo(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenInfo___elambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_Lean_Parser_FirstTokens_seq___main(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_andthen(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_andthenInfo(x_4, x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_andthen___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_Parser_andthen(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_nodeFn___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::apply_3(x_2, x_3, x_4, x_5);
x_9 = l_Lean_Parser_ParserState_mkNode(x_8, x_1, x_7);
return x_9;
}
}
obj* l_Lean_Parser_nodeFn___main(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___main___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_nodeFn___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_nodeFn___main(x_2);
return x_3;
}
}
obj* l_Lean_Parser_nodeFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::apply_3(x_2, x_3, x_4, x_5);
x_9 = l_Lean_Parser_ParserState_mkNode(x_8, x_1, x_7);
return x_9;
}
}
obj* l_Lean_Parser_nodeFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_nodeFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_nodeFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_nodeInfo(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::inc(x_3);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
}
obj* l_Lean_Parser_node(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_nodeInfo(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_node___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_Parser_node(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_orelseFn___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::apply_3(x_1, x_3, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_11; uint8 x_12; 
lean::dec(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_12 = lean::nat_dec_eq(x_11, x_8);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_13; obj* x_14; 
x_13 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
x_14 = lean::apply_3(x_2, x_3, x_4, x_13);
return x_14;
}
}
}
}
obj* l_Lean_Parser_orelseFn___main(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___main___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_orelseFn___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_orelseFn___main(x_2);
return x_3;
}
}
obj* l_Lean_Parser_orelseFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::apply_3(x_1, x_3, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_11; uint8 x_12; 
lean::dec(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_12 = lean::nat_dec_eq(x_11, x_8);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_13; obj* x_14; 
x_13 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
x_14 = lean::apply_3(x_2, x_3, x_4, x_13);
return x_14;
}
}
}
}
obj* l_Lean_Parser_orelseFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_orelseFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_orelseFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_orelseInfo___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::apply_1(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::apply_1(x_10, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_orelseInfo(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseInfo___elambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_Lean_Parser_FirstTokens_merge___main(x_4, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_orelse(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = l_Lean_Parser_orelseInfo(x_4, x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_orelse___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_Parser_orelse(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_noFirstTokenInfo(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::dec(x_3);
x_4 = lean::box(1);
lean::cnstr_set(x_1, 1, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::box(1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
}
obj* l_Lean_Parser_tryFn___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_7 = lean::array_get_size(x_5);
lean::dec(x_5);
x_8 = lean::apply_3(x_1, x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_7);
lean::dec(x_6);
return x_8;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_8, 0);
x_12 = lean::cnstr_get(x_8, 3);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_8, 1);
lean::dec(x_13);
x_14 = l_Array_shrink___main___rarg(x_11, x_7);
lean::dec(x_7);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 0, x_14);
return x_8;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_8, 0);
x_16 = lean::cnstr_get(x_8, 2);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_8);
x_17 = l_Array_shrink___main___rarg(x_15, x_7);
lean::dec(x_7);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
lean::cnstr_set(x_18, 2, x_16);
lean::cnstr_set(x_18, 3, x_9);
return x_18;
}
}
}
}
obj* l_Lean_Parser_tryFn___main(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___main___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_tryFn___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_tryFn___main(x_2);
return x_3;
}
}
obj* l_Lean_Parser_tryFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_7 = lean::array_get_size(x_5);
lean::dec(x_5);
x_8 = lean::apply_3(x_1, x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_7);
lean::dec(x_6);
return x_8;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_8, 0);
x_12 = lean::cnstr_get(x_8, 3);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_8, 1);
lean::dec(x_13);
x_14 = l_Array_shrink___main___rarg(x_11, x_7);
lean::dec(x_7);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 0, x_14);
return x_8;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_8, 0);
x_16 = lean::cnstr_get(x_8, 2);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_8);
x_17 = l_Array_shrink___main___rarg(x_15, x_7);
lean::dec(x_7);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
lean::cnstr_set(x_18, 2, x_16);
lean::cnstr_set(x_18, 3, x_9);
return x_18;
}
}
}
}
obj* l_Lean_Parser_tryFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_tryFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_tryFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_try(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Parser_noFirstTokenInfo(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryFn___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_try___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_try(x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_optionalFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_8 = lean::apply_3(x_1, x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_7);
x_10 = l_Lean_nullKind;
x_11 = l_Lean_Parser_ParserState_mkNode(x_8, x_10, x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_9);
x_12 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_6);
return x_14;
}
}
}
obj* l_Lean_Parser_optionalFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_optionalFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_optionalFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_optional(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Parser_noFirstTokenInfo(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_optional___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_optional(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_manyAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid 'many' parser combinator application, parser did not consume anything");
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::apply_3(x_2, x_3, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; uint8 x_12; 
lean::dec(x_7);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_12 = lean::nat_dec_eq(x_8, x_11);
lean::dec(x_11);
lean::dec(x_8);
if (x_12 == 0)
{
x_5 = x_9;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_14 = l_Lean_Parser_manyAux___main___closed__1;
x_15 = l_Lean_Parser_ParserState_mkError(x_9, x_14);
return x_15;
}
}
else
{
obj* x_16; 
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_16 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
return x_16;
}
}
}
obj* l_Lean_Parser_manyAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_manyAux___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_manyAux(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_manyAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_manyAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_manyAux(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_manyFn(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_manyAux___main(x_1, x_2, x_3, x_4, x_5);
x_9 = l_Lean_nullKind;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_7);
return x_10;
}
}
obj* l_Lean_Parser_manyFn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_manyFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_many(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = l_Lean_Parser_noFirstTokenInfo(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::box(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_manyFn___boxed), 5, 2);
lean::closure_set(x_7, 0, x_6);
lean::closure_set(x_7, 1, x_5);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_many___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_many(x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_many1(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::inc(x_3);
x_4 = l_Lean_Parser_noFirstTokenInfo(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::box(x_1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_manyFn___boxed), 5, 2);
lean::closure_set(x_7, 0, x_6);
lean::closure_set(x_7, 1, x_5);
x_8 = l_Lean_Parser_andthenInfo(x_3, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean::closure_set(x_9, 0, x_5);
lean::closure_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_many1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_many1(x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main(uint8 x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5, uint8 x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::array_get_size(x_10);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_7);
x_13 = lean::apply_3(x_2, x_7, x_8, x_9);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_12);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::array_get_size(x_15);
lean::dec(x_15);
x_17 = lean::cnstr_get(x_13, 1);
lean::inc(x_17);
lean::inc(x_3);
lean::inc(x_8);
lean::inc(x_7);
x_18 = lean::apply_3(x_3, x_7, x_8, x_13);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
lean::dec(x_17);
lean::dec(x_16);
{
uint8 _tmp_5 = x_4;
obj* _tmp_8 = x_18;
x_6 = _tmp_5;
x_9 = _tmp_8;
}
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_19);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_21 = l_Lean_Parser_ParserState_restore(x_18, x_16, x_17);
lean::dec(x_16);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_5);
return x_23;
}
}
else
{
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
if (x_6 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_12);
lean::dec(x_11);
x_24 = lean::box(0);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_24);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_5);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
lean::dec(x_11);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_5);
return x_30;
}
}
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; uint8 x_12; obj* x_13; 
x_10 = lean::unbox(x_1);
lean::dec(x_1);
x_11 = lean::unbox(x_4);
lean::dec(x_4);
x_12 = lean::unbox(x_6);
lean::dec(x_6);
x_13 = l___private_init_lean_parser_parser_1__sepByFnAux___main(x_10, x_2, x_3, x_11, x_5, x_12, x_7, x_8, x_9);
return x_13;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux(uint8 x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5, uint8 x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l___private_init_lean_parser_parser_1__sepByFnAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; uint8 x_12; obj* x_13; 
x_10 = lean::unbox(x_1);
lean::dec(x_1);
x_11 = lean::unbox(x_4);
lean::dec(x_4);
x_12 = lean::unbox(x_6);
lean::dec(x_6);
x_13 = l___private_init_lean_parser_parser_1__sepByFnAux(x_10, x_2, x_3, x_11, x_5, x_12, x_7, x_8, x_9);
return x_13;
}
}
obj* l_Lean_Parser_sepByFn___main(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = 1;
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main(x_1, x_3, x_4, x_2, x_9, x_10, x_5, x_6, x_7);
return x_11;
}
}
obj* l_Lean_Parser_sepByFn___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; obj* x_10; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = l_Lean_Parser_sepByFn___main(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
obj* l_Lean_Parser_sepByFn(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_sepByFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_sepByFn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; obj* x_10; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = l_Lean_Parser_sepByFn(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
obj* l_Lean_Parser_sepBy1Fn___main(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = 0;
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main(x_1, x_3, x_4, x_2, x_9, x_10, x_5, x_6, x_7);
return x_11;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; obj* x_10; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = l_Lean_Parser_sepBy1Fn___main(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
obj* l_Lean_Parser_sepBy1Fn(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_sepBy1Fn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_sepBy1Fn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; obj* x_10; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = l_Lean_Parser_sepBy1Fn(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
obj* l_Lean_Parser_sepByInfo___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::apply_1(x_10, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_sepByInfo(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepByInfo___elambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::box(1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_sepBy1Info___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::apply_1(x_10, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_sepBy1Info(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Info___elambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_1, 0);
lean::dec(x_5);
lean::cnstr_set(x_1, 0, x_3);
return x_1;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
}
obj* l_Lean_Parser_sepBy(uint8 x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = l_Lean_Parser_sepByInfo(x_5, x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::box(x_1);
x_11 = lean::box(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepByFn___boxed), 7, 4);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_11);
lean::closure_set(x_12, 2, x_8);
lean::closure_set(x_12, 3, x_9);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_sepBy___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_Parser_sepBy(x_5, x_2, x_3, x_6);
return x_7;
}
}
obj* l_Lean_Parser_sepBy1(uint8 x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = l_Lean_Parser_sepBy1Info(x_5, x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::box(x_1);
x_11 = lean::box(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_sepBy1Fn___boxed), 7, 4);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_11);
lean::closure_set(x_12, 2, x_8);
lean::closure_set(x_12, 3, x_9);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_sepBy1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_Parser_sepBy1(x_5, x_2, x_3, x_6);
return x_7;
}
}
obj* l_Lean_Parser_satisfyFn___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::string_utf8_at_end(x_6, x_5);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_8 = lean::string_utf8_get(x_6, x_5);
x_9 = lean::box_uint32(x_8);
x_10 = lean::apply_1(x_1, x_9);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_5);
x_12 = l_Lean_Parser_ParserState_mkError(x_4, x_2);
return x_12;
}
else
{
obj* x_13; 
lean::dec(x_2);
x_13 = l_Lean_Parser_ParserState_next(x_4, x_6, x_5);
lean::dec(x_5);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_14 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_15 = l_Lean_Parser_ParserState_mkError(x_4, x_14);
return x_15;
}
}
}
obj* l_Lean_Parser_satisfyFn___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_satisfyFn___main(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_satisfyFn(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_satisfyFn___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_Parser_satisfyFn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_takeUntilFn___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::string_utf8_at_end(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::string_utf8_get(x_5, x_4);
x_8 = lean::box_uint32(x_7);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; 
x_11 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
x_3 = x_11;
goto _start;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_takeUntilFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::string_utf8_at_end(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::string_utf8_get(x_5, x_4);
x_8 = lean::box_uint32(x_7);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_11; 
x_11 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
x_3 = x_11;
goto _start;
}
}
else
{
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
}
}
obj* l_Lean_Parser_takeWhileFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeWhileFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_takeWhileFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeWhile1Fn(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = l_Lean_Parser_satisfyFn___main(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(x_1, x_3, x_5);
return x_7;
}
else
{
lean::dec(x_6);
lean::dec(x_1);
return x_5;
}
}
}
obj* l_Lean_Parser_takeWhile1Fn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_takeWhile1Fn(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_finishCommentBlock___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; uint32 x_9; uint8 x_10; uint8 x_41; 
x_7 = lean::string_utf8_get(x_4, x_5);
x_8 = lean::string_utf8_next(x_4, x_5);
lean::dec(x_5);
x_9 = 45;
x_41 = x_7 == x_9;
if (x_41 == 0)
{
uint8 x_42; 
x_42 = 0;
x_10 = x_42;
goto block_40;
}
else
{
uint8 x_43; 
x_43 = 1;
x_10 = x_43;
goto block_40;
}
block_40:
{
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 47;
x_12 = x_7 == x_11;
if (x_12 == 0)
{
obj* x_13; 
x_13 = l_Lean_Parser_ParserState_setPos(x_3, x_8);
x_3 = x_13;
goto _start;
}
else
{
uint8 x_15; 
x_15 = lean::string_utf8_at_end(x_4, x_8);
if (x_15 == 0)
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_utf8_get(x_4, x_8);
x_17 = x_16 == x_9;
if (x_17 == 0)
{
obj* x_18; 
x_18 = l_Lean_Parser_ParserState_setPos(x_3, x_8);
x_3 = x_18;
goto _start;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_add(x_1, x_20);
lean::dec(x_1);
x_22 = l_Lean_Parser_ParserState_next(x_3, x_4, x_8);
lean::dec(x_8);
x_1 = x_21;
x_3 = x_22;
goto _start;
}
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_8);
lean::dec(x_1);
x_24 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_25 = l_Lean_Parser_ParserState_mkError(x_3, x_24);
return x_25;
}
}
}
else
{
uint8 x_26; 
x_26 = lean::string_utf8_at_end(x_4, x_8);
if (x_26 == 0)
{
uint32 x_27; uint32 x_28; uint8 x_29; 
x_27 = lean::string_utf8_get(x_4, x_8);
x_28 = 47;
x_29 = x_27 == x_28;
if (x_29 == 0)
{
obj* x_30; 
x_30 = l_Lean_Parser_ParserState_next(x_3, x_4, x_8);
lean::dec(x_8);
x_3 = x_30;
goto _start;
}
else
{
obj* x_32; uint8 x_33; 
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::nat_dec_eq(x_1, x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::nat_sub(x_1, x_32);
lean::dec(x_1);
x_35 = l_Lean_Parser_ParserState_next(x_3, x_4, x_8);
lean::dec(x_8);
x_1 = x_34;
x_3 = x_35;
goto _start;
}
else
{
obj* x_37; 
lean::dec(x_1);
x_37 = l_Lean_Parser_ParserState_next(x_3, x_4, x_8);
lean::dec(x_8);
return x_37;
}
}
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_8);
lean::dec(x_1);
x_38 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_39 = l_Lean_Parser_ParserState_mkError(x_3, x_38);
return x_39;
}
}
}
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_5);
lean::dec(x_1);
x_44 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_45 = l_Lean_Parser_ParserState_mkError(x_3, x_44);
return x_45;
}
}
}
obj* l_Lean_Parser_finishCommentBlock___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_finishCommentBlock(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_finishCommentBlock___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint32 x_7; uint8 x_8; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_7 = 10;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_9;
goto _start;
}
else
{
lean::dec(x_3);
return x_2;
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_whitespace___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::string_utf8_at_end(x_3, x_4);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_3, x_4);
x_7 = l_Char_isWhitespace(x_6);
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; uint8 x_35; 
x_8 = 45;
x_35 = x_6 == x_8;
if (x_35 == 0)
{
uint8 x_36; 
x_36 = 0;
x_9 = x_36;
goto block_34;
}
else
{
uint8 x_37; 
x_37 = 1;
x_9 = x_37;
goto block_34;
}
block_34:
{
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; uint8 x_24; 
x_10 = 47;
x_24 = x_6 == x_10;
if (x_24 == 0)
{
uint8 x_25; 
x_25 = 0;
x_11 = x_25;
goto block_23;
}
else
{
uint8 x_26; 
x_26 = 1;
x_11 = x_26;
goto block_23;
}
block_23:
{
if (x_11 == 0)
{
lean::dec(x_4);
return x_2;
}
else
{
obj* x_12; uint32 x_13; uint8 x_14; 
x_12 = lean::string_utf8_next(x_3, x_4);
lean::dec(x_4);
x_13 = lean::string_utf8_get(x_3, x_12);
x_14 = x_13 == x_8;
if (x_14 == 0)
{
lean::dec(x_12);
return x_2;
}
else
{
obj* x_15; uint32 x_16; uint8 x_17; 
x_15 = lean::string_utf8_next(x_3, x_12);
lean::dec(x_12);
x_16 = lean::string_utf8_get(x_3, x_15);
x_17 = x_16 == x_8;
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = l_Lean_Parser_ParserState_next(x_2, x_3, x_15);
lean::dec(x_15);
x_19 = lean::mk_nat_obj(1u);
x_20 = l_Lean_Parser_finishCommentBlock___main(x_19, x_1, x_18);
x_21 = lean::cnstr_get(x_20, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
x_2 = x_20;
goto _start;
}
else
{
lean::dec(x_21);
return x_20;
}
}
else
{
lean::dec(x_15);
return x_2;
}
}
}
}
}
else
{
obj* x_27; uint32 x_28; uint8 x_29; 
x_27 = lean::string_utf8_next(x_3, x_4);
lean::dec(x_4);
x_28 = lean::string_utf8_get(x_3, x_27);
x_29 = x_28 == x_8;
if (x_29 == 0)
{
lean::dec(x_27);
return x_2;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = l_Lean_Parser_ParserState_next(x_2, x_3, x_27);
lean::dec(x_27);
x_31 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(x_1, x_30);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
x_2 = x_31;
goto _start;
}
else
{
lean::dec(x_32);
return x_31;
}
}
}
}
}
else
{
obj* x_38; 
x_38 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
x_2 = x_38;
goto _start;
}
}
else
{
lean::dec(x_4);
return x_2;
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_whitespace___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_whitespace___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_whitespace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_whitespace___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_whitespace___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_whitespace(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_mkEmptySubstringAt(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
lean::inc(x_2);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___main___rarg(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::inc(x_1, 2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_1);
lean::cnstr_set(x_8, 2, x_1);
x_9 = lean::string_utf8_extract(x_6, x_1, x_7);
if (x_2 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_7);
lean::inc(x_6);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_7);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
x_14 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = l_Lean_Parser_whitespace___main(x_4, x_5);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::inc(x_6);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_7);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_1);
lean::cnstr_set(x_18, 2, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_9);
x_21 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_20);
return x_21;
}
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___main(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parser_2__rawAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l___private_init_lean_parser_parser_2__rawAux___main___rarg(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l___private_init_lean_parser_parser_2__rawAux___main(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___rarg(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_parser_2__rawAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parser_2__rawAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l___private_init_lean_parser_parser_2__rawAux___rarg(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l___private_init_lean_parser_parser_2__rawAux___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l___private_init_lean_parser_parser_2__rawAux(x_2);
return x_3;
}
}
obj* l_Lean_Parser_rawFn___main___rarg(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::apply_3(x_1, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l___private_init_lean_parser_parser_2__rawAux___main___rarg(x_6, x_2, x_3, x_4, x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_9;
}
else
{
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
}
obj* l_Lean_Parser_rawFn___main(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawFn___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawFn___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_rawFn___main___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_rawFn___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_rawFn___main(x_2);
return x_3;
}
}
obj* l_Lean_Parser_rawFn___rarg(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::apply_3(x_1, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l___private_init_lean_parser_parser_2__rawAux___main___rarg(x_6, x_2, x_3, x_4, x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_9;
}
else
{
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
}
obj* l_Lean_Parser_rawFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawFn___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawFn___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_rawFn___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_rawFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_rawFn(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_hexDigitFn___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid hexadecimal numeral, hexadecimal digit expected");
return x_1;
}
}
obj* l_Lean_Parser_hexDigitFn___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::string_utf8_at_end(x_3, x_4);
if (x_5 == 0)
{
uint32 x_6; obj* x_7; obj* x_8; uint8 x_19; 
x_6 = lean::string_utf8_get(x_3, x_4);
x_7 = lean::string_utf8_next(x_3, x_4);
lean::dec(x_4);
x_19 = l_Char_isDigit(x_6);
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 97;
x_21 = x_20 <= x_6;
if (x_21 == 0)
{
obj* x_22; 
x_22 = lean::box(0);
x_8 = x_22;
goto block_18;
}
else
{
uint32 x_23; uint8 x_24; 
x_23 = 102;
x_24 = x_6 <= x_23;
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::box(0);
x_8 = x_25;
goto block_18;
}
else
{
obj* x_26; 
x_26 = l_Lean_Parser_ParserState_setPos(x_2, x_7);
return x_26;
}
}
}
else
{
obj* x_27; 
x_27 = l_Lean_Parser_ParserState_setPos(x_2, x_7);
return x_27;
}
block_18:
{
uint32 x_9; uint8 x_10; 
lean::dec(x_8);
x_9 = 65;
x_10 = x_9 <= x_6;
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_7);
x_11 = l_Lean_Parser_hexDigitFn___main___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_2, x_11);
return x_12;
}
else
{
uint32 x_13; uint8 x_14; 
x_13 = 70;
x_14 = x_6 <= x_13;
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_7);
x_15 = l_Lean_Parser_hexDigitFn___main___closed__1;
x_16 = l_Lean_Parser_ParserState_mkError(x_2, x_15);
return x_16;
}
else
{
obj* x_17; 
x_17 = l_Lean_Parser_ParserState_setPos(x_2, x_7);
return x_17;
}
}
}
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_4);
x_28 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_29 = l_Lean_Parser_ParserState_mkError(x_2, x_28);
return x_29;
}
}
}
obj* l_Lean_Parser_hexDigitFn___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_hexDigitFn___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_hexDigitFn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_hexDigitFn___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_hexDigitFn___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_hexDigitFn(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_quotedCharFn___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid escape sequence");
return x_1;
}
}
obj* l_Lean_Parser_quotedCharFn___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::string_utf8_at_end(x_3, x_4);
if (x_5 == 0)
{
uint32 x_6; uint32 x_7; uint8 x_8; uint8 x_49; 
x_6 = lean::string_utf8_get(x_3, x_4);
x_7 = 92;
x_49 = x_6 == x_7;
if (x_49 == 0)
{
uint8 x_50; 
x_50 = 0;
x_8 = x_50;
goto block_48;
}
else
{
uint8 x_51; 
x_51 = 1;
x_8 = x_51;
goto block_48;
}
block_48:
{
if (x_8 == 0)
{
uint32 x_9; uint8 x_10; uint8 x_44; 
x_9 = 34;
x_44 = x_6 == x_9;
if (x_44 == 0)
{
uint8 x_45; 
x_45 = 0;
x_10 = x_45;
goto block_43;
}
else
{
uint8 x_46; 
x_46 = 1;
x_10 = x_46;
goto block_43;
}
block_43:
{
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 39;
x_12 = x_6 == x_11;
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 10;
x_14 = x_6 == x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = 9;
x_16 = x_6 == x_15;
if (x_16 == 0)
{
uint32 x_17; uint8 x_18; uint8 x_36; 
x_17 = 120;
x_36 = x_6 == x_17;
if (x_36 == 0)
{
uint8 x_37; 
x_37 = 0;
x_18 = x_37;
goto block_35;
}
else
{
uint8 x_38; 
x_38 = 1;
x_18 = x_38;
goto block_35;
}
block_35:
{
if (x_18 == 0)
{
uint32 x_19; uint8 x_20; 
x_19 = 117;
x_20 = x_6 == x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_4);
x_21 = l_Lean_Parser_quotedCharFn___main___closed__1;
x_22 = l_Lean_Parser_ParserState_mkError(x_2, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
x_24 = l_Lean_Parser_hexDigitFn___main(x_1, x_23);
x_25 = lean::cnstr_get(x_24, 3);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
x_26 = l_Lean_Parser_hexDigitFn___main(x_1, x_24);
x_27 = lean::cnstr_get(x_26, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; 
x_28 = l_Lean_Parser_hexDigitFn___main(x_1, x_26);
x_29 = lean::cnstr_get(x_28, 3);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; 
x_30 = l_Lean_Parser_hexDigitFn___main(x_1, x_28);
return x_30;
}
else
{
lean::dec(x_29);
return x_28;
}
}
else
{
lean::dec(x_27);
return x_26;
}
}
else
{
lean::dec(x_25);
return x_24;
}
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
x_32 = l_Lean_Parser_hexDigitFn___main(x_1, x_31);
x_33 = lean::cnstr_get(x_32, 3);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_hexDigitFn___main(x_1, x_32);
return x_34;
}
else
{
lean::dec(x_33);
return x_32;
}
}
}
}
else
{
obj* x_39; 
x_39 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
return x_39;
}
}
else
{
obj* x_40; 
x_40 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
return x_40;
}
}
else
{
obj* x_41; 
x_41 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
return x_41;
}
}
else
{
obj* x_42; 
x_42 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
return x_42;
}
}
}
else
{
obj* x_47; 
x_47 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_4);
return x_47;
}
}
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_4);
x_52 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_53 = l_Lean_Parser_ParserState_mkError(x_2, x_52);
return x_53;
}
}
}
obj* l_Lean_Parser_quotedCharFn___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_quotedCharFn___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_quotedCharFn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_quotedCharFn___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_quotedCharFn___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_quotedCharFn(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_strLitKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("strLit");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_numLitKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("numLit");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkNodeToken(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::inc(x_2, 2);
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_2);
x_8 = lean::string_utf8_extract(x_5, x_2, x_6);
x_9 = l_Lean_Parser_whitespace___main(x_3, x_4);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::inc(x_5);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_2);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_8);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::mk_array(x_15, x_14);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParserState_pushSyntax(x_9, x_18);
return x_19;
}
}
obj* l_Lean_Parser_mkNodeToken___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_mkNodeToken(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_strLitFnAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; obj* x_9; uint32 x_10; uint8 x_11; 
x_7 = lean::string_utf8_get(x_4, x_5);
x_8 = lean::string_utf8_next(x_4, x_5);
lean::dec(x_5);
x_9 = l_Lean_Parser_ParserState_setPos(x_3, x_8);
x_10 = 34;
x_11 = x_7 == x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 92;
x_13 = x_7 == x_12;
if (x_13 == 0)
{
x_3 = x_9;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_Lean_Parser_quotedCharFn___main(x_2, x_9);
x_16 = lean::cnstr_get(x_15, 3);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
x_3 = x_15;
goto _start;
}
else
{
lean::dec(x_16);
lean::dec(x_1);
return x_15;
}
}
}
else
{
obj* x_18; obj* x_19; 
x_18 = l_Lean_Parser_strLitKind;
x_19 = l_Lean_Parser_mkNodeToken(x_18, x_1, x_2, x_9);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_5);
lean::dec(x_1);
x_20 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_21 = l_Lean_Parser_ParserState_mkError(x_3, x_20);
return x_21;
}
}
}
obj* l_Lean_Parser_strLitFnAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_strLitFnAux___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_strLitFnAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_strLitFnAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_strLitFnAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_strLitFnAux(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_7 = l_Char_isDigit(x_6);
if (x_7 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_8; 
x_8 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_8;
goto _start;
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_decimalNumberFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; uint32 x_7; uint32 x_8; uint8 x_9; 
x_4 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_2, x_3);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_7 = lean::string_utf8_get(x_5, x_6);
x_8 = 46;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_4);
return x_11;
}
else
{
obj* x_12; uint32 x_13; uint8 x_14; 
x_12 = lean::string_utf8_next(x_5, x_6);
lean::dec(x_6);
x_13 = lean::string_utf8_get(x_5, x_12);
x_14 = l_Char_isDigit(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_12);
x_15 = l_Lean_Parser_numLitKind;
x_16 = l_Lean_Parser_mkNodeToken(x_15, x_1, x_2, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = l_Lean_Parser_ParserState_setPos(x_4, x_12);
x_18 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_2, x_17);
x_19 = l_Lean_Parser_numLitKind;
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_1, x_2, x_18);
return x_20;
}
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_decimalNumberFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_decimalNumberFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::string_utf8_at_end(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_get(x_5, x_4);
x_8 = 48;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = 49;
x_11 = x_7 == x_10;
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_4);
x_12 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_12;
}
else
{
obj* x_13; 
lean::dec(x_1);
x_13 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_13;
}
}
else
{
obj* x_14; 
lean::dec(x_1);
x_14 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_16 = l_Lean_Parser_ParserState_mkError(x_3, x_15);
return x_16;
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint32 x_7; uint8 x_8; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_7 = 48;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint32 x_9; uint8 x_10; 
x_9 = 49;
x_10 = x_6 == x_9;
if (x_10 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_11; 
x_11 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_11;
goto _start;
}
}
else
{
obj* x_13; 
x_13 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_binNumberFn___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected binary number");
return x_1;
}
}
obj* l_Lean_Parser_binNumberFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_binNumberFn___closed__1;
x_5 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1(x_4, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(x_2, x_5);
x_8 = l_Lean_Parser_numLitKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_5);
return x_11;
}
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_binNumberFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_binNumberFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::string_utf8_at_end(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_get(x_5, x_4);
x_8 = 48;
x_9 = x_8 <= x_7;
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_4);
x_10 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = 55;
x_12 = x_7 <= x_11;
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_4);
x_13 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_1);
x_14 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_14;
}
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_16 = l_Lean_Parser_ParserState_mkError(x_3, x_15);
return x_16;
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint32 x_7; uint8 x_8; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_7 = 48;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = 55;
x_10 = x_6 <= x_9;
if (x_10 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_11; 
x_11 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_11;
goto _start;
}
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_octalNumberFn___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected octal number");
return x_1;
}
}
obj* l_Lean_Parser_octalNumberFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_octalNumberFn___closed__1;
x_5 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1(x_4, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(x_2, x_5);
x_8 = l_Lean_Parser_numLitKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_5);
return x_11;
}
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_octalNumberFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_octalNumberFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::string_utf8_at_end(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; uint32 x_30; uint8 x_31; 
x_7 = lean::string_utf8_get(x_5, x_4);
x_30 = 48;
x_31 = x_30 <= x_7;
if (x_31 == 0)
{
uint8 x_32; 
x_32 = 0;
x_8 = x_32;
goto block_29;
}
else
{
uint32 x_33; uint8 x_34; 
x_33 = 57;
x_34 = x_7 <= x_33;
if (x_34 == 0)
{
x_8 = x_34;
goto block_29;
}
else
{
obj* x_35; 
lean::dec(x_1);
x_35 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_35;
}
}
block_29:
{
uint32 x_9; uint8 x_10; 
x_9 = 97;
x_10 = x_9 <= x_7;
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 65;
x_12 = x_11 <= x_7;
if (x_12 == 0)
{
if (x_8 == 0)
{
obj* x_13; 
lean::dec(x_4);
x_13 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_1);
x_14 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_14;
}
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = 70;
x_16 = x_7 <= x_15;
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_4);
x_17 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_17;
}
else
{
obj* x_18; 
lean::dec(x_1);
x_18 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_18;
}
}
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = 102;
x_20 = x_7 <= x_19;
if (x_20 == 0)
{
uint32 x_21; uint8 x_22; 
x_21 = 65;
x_22 = x_21 <= x_7;
if (x_22 == 0)
{
obj* x_23; 
lean::dec(x_4);
x_23 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_23;
}
else
{
uint32 x_24; uint8 x_25; 
x_24 = 70;
x_25 = x_7 <= x_24;
if (x_25 == 0)
{
obj* x_26; 
lean::dec(x_4);
x_26 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_26;
}
else
{
obj* x_27; 
lean::dec(x_1);
x_27 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_27;
}
}
}
else
{
obj* x_28; 
lean::dec(x_1);
x_28 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_28;
}
}
}
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_4);
lean::dec(x_1);
x_36 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_37 = l_Lean_Parser_ParserState_mkError(x_3, x_36);
return x_37;
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; uint32 x_29; uint8 x_30; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_29 = 48;
x_30 = x_29 <= x_6;
if (x_30 == 0)
{
uint8 x_31; 
x_31 = 0;
x_7 = x_31;
goto block_28;
}
else
{
uint32 x_32; uint8 x_33; 
x_32 = 57;
x_33 = x_6 <= x_32;
if (x_33 == 0)
{
x_7 = x_33;
goto block_28;
}
else
{
obj* x_34; 
x_34 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_34;
goto _start;
}
}
block_28:
{
uint32 x_8; uint8 x_9; 
x_8 = 97;
x_9 = x_8 <= x_6;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = 65;
x_11 = x_10 <= x_6;
if (x_11 == 0)
{
if (x_7 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_12; 
x_12 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_12;
goto _start;
}
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 70;
x_15 = x_6 <= x_14;
if (x_15 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_16; 
x_16 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_16;
goto _start;
}
}
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = 102;
x_19 = x_6 <= x_18;
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 65;
x_21 = x_20 <= x_6;
if (x_21 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
uint32 x_22; uint8 x_23; 
x_22 = 70;
x_23 = x_6 <= x_22;
if (x_23 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_24; 
x_24 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_24;
goto _start;
}
}
}
else
{
obj* x_26; 
x_26 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_26;
goto _start;
}
}
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_hexNumberFn___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected hexadecimal number");
return x_1;
}
}
obj* l_Lean_Parser_hexNumberFn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_hexNumberFn___closed__1;
x_5 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1(x_4, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(x_2, x_5);
x_8 = l_Lean_Parser_numLitKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_5);
return x_11;
}
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_hexNumberFn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_hexNumberFn(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_numberFnAux___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected numeral");
return x_1;
}
}
obj* l_Lean_Parser_numberFnAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::string_utf8_at_end(x_3, x_4);
if (x_5 == 0)
{
uint32 x_6; uint32 x_7; uint8 x_8; 
x_6 = lean::string_utf8_get(x_3, x_4);
x_7 = 48;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Char_isDigit(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_4);
x_10 = l_Lean_Parser_numberFnAux___closed__1;
x_11 = l_Lean_Parser_ParserState_mkError(x_2, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; 
x_12 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
x_13 = l_Lean_Parser_decimalNumberFn(x_4, x_1, x_12);
return x_13;
}
}
else
{
obj* x_14; uint32 x_15; uint32 x_16; uint8 x_17; 
x_14 = lean::string_utf8_next(x_3, x_4);
x_15 = lean::string_utf8_get(x_3, x_14);
x_16 = 98;
x_17 = x_15 == x_16;
if (x_17 == 0)
{
uint32 x_18; uint8 x_19; 
x_18 = 66;
x_19 = x_15 == x_18;
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; uint8 x_39; 
x_20 = 111;
x_39 = x_15 == x_20;
if (x_39 == 0)
{
uint8 x_40; 
x_40 = 0;
x_21 = x_40;
goto block_38;
}
else
{
uint8 x_41; 
x_41 = 1;
x_21 = x_41;
goto block_38;
}
block_38:
{
if (x_21 == 0)
{
uint32 x_22; uint8 x_23; 
x_22 = 79;
x_23 = x_15 == x_22;
if (x_23 == 0)
{
uint32 x_24; uint8 x_25; 
x_24 = 120;
x_25 = x_15 == x_24;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = 88;
x_27 = x_15 == x_26;
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = l_Lean_Parser_ParserState_setPos(x_2, x_14);
x_29 = l_Lean_Parser_decimalNumberFn(x_4, x_1, x_28);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = l_Lean_Parser_ParserState_next(x_2, x_3, x_14);
lean::dec(x_14);
x_31 = l_Lean_Parser_hexNumberFn(x_4, x_1, x_30);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_Lean_Parser_ParserState_next(x_2, x_3, x_14);
lean::dec(x_14);
x_33 = l_Lean_Parser_hexNumberFn(x_4, x_1, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_Lean_Parser_ParserState_next(x_2, x_3, x_14);
lean::dec(x_14);
x_35 = l_Lean_Parser_octalNumberFn(x_4, x_1, x_34);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; 
x_36 = l_Lean_Parser_ParserState_next(x_2, x_3, x_14);
lean::dec(x_14);
x_37 = l_Lean_Parser_octalNumberFn(x_4, x_1, x_36);
return x_37;
}
}
}
else
{
obj* x_42; obj* x_43; 
x_42 = l_Lean_Parser_ParserState_next(x_2, x_3, x_14);
lean::dec(x_14);
x_43 = l_Lean_Parser_binNumberFn(x_4, x_1, x_42);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; 
x_44 = l_Lean_Parser_ParserState_next(x_2, x_3, x_14);
lean::dec(x_14);
x_45 = l_Lean_Parser_binNumberFn(x_4, x_1, x_44);
return x_45;
}
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_4);
x_46 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_47 = l_Lean_Parser_ParserState_mkError(x_2, x_46);
return x_47;
}
}
}
obj* l_Lean_Parser_numberFnAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_Parser_isIdCont___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint32 x_4; uint32 x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = lean::string_utf8_get(x_1, x_3);
x_5 = 46;
x_6 = x_4 == x_5;
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
obj* x_8; uint8 x_9; 
x_8 = lean::string_utf8_next(x_1, x_3);
x_9 = lean::string_utf8_at_end(x_1, x_8);
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_utf8_get(x_1, x_8);
lean::dec(x_8);
x_11 = l_Lean_isIdFirst(x_10);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = l_Lean_isIdBeginEscape(x_10);
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8 x_14; 
lean::dec(x_8);
x_14 = 0;
return x_14;
}
}
}
}
obj* l_Lean_Parser_isIdCont___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Parser_isIdCont___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_Parser_isIdCont(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Parser_isIdCont___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_isIdCont___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Parser_isIdCont(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l___private_init_lean_parser_parser_3__isToken___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::nat_sub(x_1, x_1);
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::string_utf8_byte_size(x_6);
x_8 = lean::nat_dec_le(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
return x_8;
}
}
}
obj* l___private_init_lean_parser_parser_3__isToken(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parser_3__isToken___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parser_3__isToken___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l___private_init_lean_parser_parser_3__isToken___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_parser_3__isToken___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_parser_3__isToken(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_mkTokenAndFixPos___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("token expected");
return x_1;
}
}
obj* l_Lean_Parser_mkTokenAndFixPos(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_mkTokenAndFixPos___closed__1;
x_6 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_5, x_1);
return x_6;
}
else
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_1, 2);
lean::inc(x_9);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_1);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_12 = lean::string_utf8_byte_size(x_11);
x_13 = lean::nat_add(x_1, x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_ParserState_setPos(x_4, x_13);
x_15 = l_Lean_Parser_whitespace___main(x_3, x_14);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::inc(x_9);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_13);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_1);
lean::cnstr_set(x_18, 2, x_17);
lean::cnstr_set(x_2, 0, x_18);
x_19 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_11);
x_20 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_1, 2);
lean::inc(x_22);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_1);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
lean::dec(x_21);
x_25 = lean::string_utf8_byte_size(x_24);
x_26 = lean::nat_add(x_1, x_25);
lean::dec(x_25);
lean::inc(x_26);
x_27 = l_Lean_Parser_ParserState_setPos(x_4, x_26);
x_28 = l_Lean_Parser_whitespace___main(x_3, x_27);
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
lean::inc(x_22);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_22);
lean::cnstr_set(x_30, 1, x_26);
lean::cnstr_set(x_30, 2, x_29);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_23);
lean::cnstr_set(x_31, 1, x_1);
lean::cnstr_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
x_34 = l_Lean_Parser_ParserState_pushSyntax(x_28, x_33);
return x_34;
}
}
}
}
obj* l_Lean_Parser_mkTokenAndFixPos___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_mkIdResult(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = l___private_init_lean_parser_parser_3__isToken___rarg(x_6, x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_2);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_8);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_6);
x_10 = l_Lean_Parser_whitespace___main(x_4, x_5);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::inc(x_1, 2);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_12, 2, x_1);
lean::inc(x_8);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_6);
lean::cnstr_set(x_13, 2, x_11);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(3, 5, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_9);
lean::cnstr_set(x_17, 2, x_3);
lean::cnstr_set(x_17, 3, x_16);
lean::cnstr_set(x_17, 4, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_10, x_17);
return x_18;
}
else
{
obj* x_19; 
lean::dec(x_6);
lean::dec(x_3);
x_19 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_19;
}
}
}
obj* l_Lean_Parser_mkIdResult___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_mkIdResult(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_7 = l_Lean_isIdRest(x_6);
if (x_7 == 0)
{
lean::dec(x_3);
return x_2;
}
else
{
obj* x_8; 
x_8 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_8;
goto _start;
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::string_utf8_at_end(x_4, x_3);
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = lean::string_utf8_get(x_4, x_3);
x_7 = l_Lean_isIdEndEscape(x_6);
if (x_7 == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_ParserState_next(x_2, x_4, x_3);
lean::dec(x_3);
x_2 = x_8;
goto _start;
}
else
{
lean::dec(x_3);
return x_2;
}
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::string_utf8_at_end(x_5, x_4);
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_5, x_4);
x_8 = l_Lean_isIdEndEscape(x_7);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_4);
x_9 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_9;
}
else
{
obj* x_10; 
lean::dec(x_1);
x_10 = l_Lean_Parser_ParserState_next(x_3, x_5, x_4);
lean::dec(x_4);
return x_10;
}
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_1);
x_11 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_3, x_11);
return x_12;
}
}
}
obj* _init_l_Lean_Parser_identFnAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("end of escaped identifier expected");
return x_1;
}
}
obj* l_Lean_Parser_identFnAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
x_8 = lean::string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_utf8_get(x_6, x_7);
x_10 = l_Lean_isIdBeginEscape(x_9);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = l_Lean_isIdFirst(x_9);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
lean::dec(x_3);
x_12 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = l_Lean_Parser_ParserState_next(x_5, x_6, x_7);
x_14 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(x_4, x_13);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::string_utf8_extract(x_6, x_7, x_15);
lean::dec(x_15);
x_17 = lean_name_mk_string(x_3, x_16);
x_18 = l_Lean_Parser_isIdCont___main(x_6, x_14);
if (x_18 == 0)
{
obj* x_19; 
lean::dec(x_1);
x_19 = l_Lean_Parser_mkIdResult(x_7, x_2, x_17, x_4, x_14);
return x_19;
}
else
{
lean::dec(x_7);
x_3 = x_17;
x_5 = x_14;
goto _start;
}
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::string_utf8_next(x_6, x_7);
lean::dec(x_7);
lean::inc(x_21);
x_22 = l_Lean_Parser_ParserState_setPos(x_5, x_21);
x_23 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(x_4, x_22);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_25 = l_Lean_Parser_identFnAux___main___closed__1;
x_26 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4(x_25, x_4, x_23);
x_27 = lean::cnstr_get(x_26, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::string_utf8_extract(x_6, x_21, x_24);
lean::dec(x_24);
lean::dec(x_21);
x_29 = lean_name_mk_string(x_3, x_28);
x_30 = l_Lean_Parser_isIdCont___main(x_6, x_26);
if (x_30 == 0)
{
obj* x_31; 
x_31 = l_Lean_Parser_mkIdResult(x_1, x_2, x_29, x_4, x_26);
return x_31;
}
else
{
x_3 = x_29;
x_5 = x_26;
goto _start;
}
}
else
{
lean::dec(x_27);
lean::dec(x_24);
lean::dec(x_21);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_26;
}
}
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_33 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_34 = l_Lean_Parser_ParserState_mkError(x_5, x_33);
return x_34;
}
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_identFnAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_identFnAux___main(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_identFnAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_identFnAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_identFnAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_identFnAux(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_lean_parser_parser_4__tokenFnAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint32 x_5; uint32 x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::string_utf8_get(x_3, x_4);
x_6 = 34;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8 x_8; 
x_8 = l_Char_isDigit(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_1, 4);
lean::inc(x_9);
lean::inc(x_4);
x_10 = l_Lean_Parser_Trie_matchPrefix___rarg(x_3, x_9, x_4);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::box(0);
x_13 = l_Lean_Parser_identFnAux___main(x_4, x_11, x_12, x_1, x_2);
lean::dec(x_1);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_4);
lean::dec(x_3);
x_14 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean::dec(x_1);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_Lean_Parser_ParserState_next(x_2, x_3, x_4);
lean::dec(x_3);
x_16 = l_Lean_Parser_strLitFnAux___main(x_4, x_1, x_15);
lean::dec(x_1);
return x_16;
}
}
}
obj* l___private_init_lean_parser_parser_4__tokenFnAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_parser_4__tokenFnAux___main(x_1, x_2);
return x_3;
}
}
obj* l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_stxInh;
x_6 = lean::array_get(x_5, x_1, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_lean_parser_parser_5__updateCache(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 3);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::array_get_size(x_4);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 3);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_2, 2);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_2, 1);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_2, 0);
lean::dec(x_13);
x_14 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_4);
lean::inc(x_5);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_5);
lean::cnstr_set(x_15, 2, x_14);
lean::cnstr_set(x_2, 2, x_15);
return x_2;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_2);
x_16 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_4);
lean::inc(x_5);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_5);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_5);
lean::cnstr_set(x_18, 2, x_17);
lean::cnstr_set(x_18, 3, x_3);
return x_18;
}
}
else
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_2;
}
}
else
{
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_tokenFn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::string_utf8_at_end(x_3, x_4);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::nat_dec_eq(x_7, x_4);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_6);
x_9 = l___private_init_lean_parser_parser_4__tokenFnAux___main(x_1, x_2);
x_10 = l___private_init_lean_parser_parser_5__updateCache(x_4, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
x_12 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Lean_Parser_ParserState_setPos(x_12, x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_16 = l_Lean_Parser_ParserState_mkError(x_2, x_15);
return x_16;
}
}
}
obj* l_Lean_Parser_peekToken(obj* x_1, obj* x_2) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean::dec(x_4);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_7);
x_13 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean::dec(x_4);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_Lean_Parser_satisfySymbolFn(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_3, x_4);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 2)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_1(x_1, x_10);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; 
x_13 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_13;
}
else
{
lean::dec(x_5);
lean::dec(x_2);
return x_6;
}
}
else
{
obj* x_14; 
lean::dec(x_9);
lean::dec(x_1);
x_14 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_7);
lean::dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_15;
}
}
}
obj* l_Lean_Parser_symbolFnAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_3, x_4);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 2)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::string_dec_eq(x_10, x_1);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; 
x_12 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_12;
}
else
{
lean::dec(x_5);
lean::dec(x_2);
return x_6;
}
}
else
{
obj* x_13; 
lean::dec(x_9);
x_13 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_13;
}
}
else
{
obj* x_14; 
lean::dec(x_7);
x_14 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_14;
}
}
}
obj* l_Lean_Parser_symbolFnAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_symbolFnAux(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_insertToken___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("precedence mismatch for '");
return x_1;
}
}
obj* _init_l_Lean_Parser_insertToken___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("', previous: ");
return x_1;
}
}
obj* _init_l_Lean_Parser_insertToken___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", new: ");
return x_1;
}
}
obj* l_Lean_Parser_insertToken(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_3);
x_5 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_1, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_6, x_3, x_4);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; 
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_2);
x_13 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_12, x_3, x_4);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_17 = lean::nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_3);
x_18 = l_Lean_Parser_insertToken___closed__1;
x_19 = lean::string_append(x_18, x_1);
lean::dec(x_1);
x_20 = l_Lean_Parser_insertToken___closed__2;
x_21 = lean::string_append(x_19, x_20);
x_22 = l_Nat_repr(x_16);
x_23 = lean::string_append(x_21, x_22);
lean::dec(x_22);
x_24 = l_Lean_Parser_insertToken___closed__3;
x_25 = lean::string_append(x_23, x_24);
x_26 = l_Nat_repr(x_15);
x_27 = lean::string_append(x_25, x_26);
lean::dec(x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
else
{
obj* x_29; 
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_1);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_3);
return x_29;
}
}
}
}
}
}
obj* l_Lean_Parser_symbolInfo(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_2);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_insertToken), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_symbolFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected '");
return x_1;
}
}
obj* l_Lean_Parser_symbolFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_6 = lean::string_append(x_5, x_1);
x_7 = l_Char_HasRepr___closed__1;
x_8 = lean::string_append(x_6, x_7);
x_9 = l_Lean_Parser_symbolFnAux(x_1, x_8, x_3, x_4);
return x_9;
}
}
obj* l_Lean_Parser_symbolFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_symbolFn___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_symbolFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_symbolFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbol(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_2, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_symbol___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_Parser_symbol(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_unicodeSymbolFnAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = l_Lean_Parser_tokenFn(x_4, x_5);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_10 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_9);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 2)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::string_dec_eq(x_11, x_1);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = lean::string_dec_eq(x_11, x_2);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_3, x_6);
return x_14;
}
else
{
lean::dec(x_6);
lean::dec(x_3);
return x_7;
}
}
else
{
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_3);
return x_7;
}
}
else
{
obj* x_15; 
lean::dec(x_10);
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_3, x_6);
return x_15;
}
}
else
{
obj* x_16; 
lean::dec(x_8);
x_16 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_3, x_6);
return x_16;
}
}
}
obj* l_Lean_Parser_unicodeSymbolFnAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_unicodeSymbolInfo___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
lean::inc(x_3);
x_5 = l_Lean_Parser_insertToken(x_1, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_3);
lean::dec(x_2);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_10 = l_Lean_Parser_insertToken(x_2, x_3, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_unicodeSymbolInfo(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolInfo___elambda__1), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_unicodeSymbolFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' or '");
return x_1;
}
}
obj* l_Lean_Parser_unicodeSymbolFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_7 = lean::string_append(x_6, x_1);
x_8 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_9 = lean::string_append(x_7, x_8);
x_10 = lean::string_append(x_9, x_2);
x_11 = l_Char_HasRepr___closed__1;
x_12 = lean::string_append(x_10, x_11);
x_13 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_12, x_4, x_5);
return x_13;
}
}
obj* l_Lean_Parser_unicodeSymbolFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_unicodeSymbolFn___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_unicodeSymbolFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_unicodeSymbolFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_unicodeSymbol(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_3);
lean::inc(x_2);
x_5 = l_Lean_Parser_unicodeSymbolInfo(x_2, x_3, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_unicodeSymbol___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_unicodeSymbol(x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Parser_mkAtomicInfo___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_mkAtomicInfo___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_mkAtomicInfo___elambda__1), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_mkAtomicInfo(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_mkAtomicInfo___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
obj* l_Lean_Parser_numLitFn___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_tokenFn(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 3);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_numLitKind;
x_8 = l_Lean_Syntax_isOfKind___main(x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_numberFnAux___closed__1;
x_10 = l_Lean_Parser_ParserState_mkError(x_3, x_9);
return x_10;
}
else
{
return x_3;
}
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_4);
x_11 = l_Lean_Parser_numberFnAux___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_3, x_11);
return x_12;
}
}
}
obj* l_Lean_Parser_numLitFn(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numLitFn___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_numLitFn___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_numLitFn(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_numLit___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("numLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
obj* l_Lean_Parser_numLit(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numLitFn___boxed), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_numLit___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_numLit___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_numLit(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_strLitFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected string literal");
return x_1;
}
}
obj* l_Lean_Parser_strLitFn___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_tokenFn(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 3);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_strLitKind;
x_8 = l_Lean_Syntax_isOfKind___main(x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_strLitFn___rarg___closed__1;
x_10 = l_Lean_Parser_ParserState_mkError(x_3, x_9);
return x_10;
}
else
{
return x_3;
}
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_4);
x_11 = l_Lean_Parser_strLitFn___rarg___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_3, x_11);
return x_12;
}
}
}
obj* l_Lean_Parser_strLitFn(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_strLitFn___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_strLitFn___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_strLitFn(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_strLit___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("strLit");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
obj* l_Lean_Parser_strLit(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_strLitFn___boxed), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_strLit___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_strLit___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_strLit(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_identFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected identifier");
return x_1;
}
}
obj* l_Lean_Parser_identFn___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_tokenFn(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 3);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_5);
lean::dec(x_5);
x_7 = l_Lean_Syntax_isIdent___main(x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_Parser_identFn___rarg___closed__1;
x_9 = l_Lean_Parser_ParserState_mkError(x_3, x_8);
return x_9;
}
else
{
return x_3;
}
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_4);
x_10 = l_Lean_Parser_identFn___rarg___closed__1;
x_11 = l_Lean_Parser_ParserState_mkError(x_3, x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_identFn(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_identFn___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_identFn(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_ident___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("ident");
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_ident___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_ident___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_ident(x_2);
return x_3;
}
}
obj* l_Lean_Parser_string2basic(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_4 = l_Lean_Parser_symbolInfo(x_2, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_string2basic___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_string2basic(x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_ParserState_keepNewError(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = l_Array_shrink___main___rarg(x_4, x_2);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_10 = l_Array_shrink___main___rarg(x_6, x_2);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_9);
return x_11;
}
}
}
obj* l_Lean_Parser_ParserState_keepNewError___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParserState_keepNewError(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_keepPrevError(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 3);
lean::dec(x_7);
x_8 = lean::cnstr_get(x_1, 1);
lean::dec(x_8);
x_9 = l_Array_shrink___main___rarg(x_6, x_2);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 1, x_3);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_12 = l_Array_shrink___main___rarg(x_10, x_2);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_3);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_4);
return x_13;
}
}
}
obj* l_Lean_Parser_ParserState_keepPrevError___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParserState_keepPrevError(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_ParserState_mergeErrors___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("; ");
return x_1;
}
}
obj* l_Lean_Parser_ParserState_mergeErrors(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 3);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
return x_1;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 3);
lean::dec(x_7);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = l_Array_shrink___main___rarg(x_6, x_2);
x_11 = l_Lean_Parser_ParserState_mergeErrors___closed__1;
x_12 = lean::string_append(x_9, x_11);
x_13 = lean::string_append(x_12, x_3);
lean::cnstr_set(x_4, 0, x_13);
lean::cnstr_set(x_1, 0, x_10);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_15 = l_Array_shrink___main___rarg(x_6, x_2);
x_16 = l_Lean_Parser_ParserState_mergeErrors___closed__1;
x_17 = lean::string_append(x_14, x_16);
x_18 = lean::string_append(x_17, x_3);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_1, 3, x_19);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::dec_ref(x_4);
 x_24 = lean::box(0);
}
x_25 = l_Array_shrink___main___rarg(x_20, x_2);
x_26 = l_Lean_Parser_ParserState_mergeErrors___closed__1;
x_27 = lean::string_append(x_23, x_26);
x_28 = lean::string_append(x_27, x_3);
if (lean::is_scalar(x_24)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_24;
}
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_21);
lean::cnstr_set(x_30, 2, x_22);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
}
}
obj* l_Lean_Parser_ParserState_mergeErrors___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParserState_mergeErrors(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_ParserState_mkLongestNodeAlt(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_eq(x_6, x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_2, x_8);
x_10 = lean::nat_dec_eq(x_6, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_1);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_1, 3);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_1, 2);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_1, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_1, 0);
lean::dec(x_15);
lean::inc(x_2);
x_16 = l_Array_extract___rarg(x_3, x_2, x_6);
lean::dec(x_6);
x_17 = lean::box(0);
x_18 = l_Lean_nullKind;
x_19 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_Array_shrink___main___rarg(x_3, x_2);
lean::dec(x_2);
x_21 = lean::array_push(x_20, x_19);
x_22 = lean::box(0);
lean::cnstr_set(x_1, 3, x_22);
lean::cnstr_set(x_1, 0, x_21);
return x_1;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::inc(x_2);
x_23 = l_Array_extract___rarg(x_3, x_2, x_6);
lean::dec(x_6);
x_24 = lean::box(0);
x_25 = l_Lean_nullKind;
x_26 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
x_27 = l_Array_shrink___main___rarg(x_3, x_2);
lean::dec(x_2);
x_28 = lean::array_push(x_27, x_26);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_4);
lean::cnstr_set(x_30, 2, x_5);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
else
{
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_1;
}
}
else
{
uint8 x_31; 
lean::dec(x_6);
lean::dec(x_2);
x_31 = !lean::is_exclusive(x_1);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_1, 3);
lean::dec(x_32);
x_33 = lean::cnstr_get(x_1, 2);
lean::dec(x_33);
x_34 = lean::cnstr_get(x_1, 1);
lean::dec(x_34);
x_35 = lean::cnstr_get(x_1, 0);
lean::dec(x_35);
x_36 = lean::box(0);
x_37 = lean::array_push(x_3, x_36);
x_38 = lean::box(0);
lean::cnstr_set(x_1, 3, x_38);
lean::cnstr_set(x_1, 0, x_37);
return x_1;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_1);
x_39 = lean::box(0);
x_40 = lean::array_push(x_3, x_39);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_4);
lean::cnstr_set(x_42, 2, x_5);
lean::cnstr_set(x_42, 3, x_41);
return x_42;
}
}
}
}
obj* l_Lean_Parser_ParserState_keepLatest(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 3);
lean::dec(x_5);
x_6 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_4);
x_7 = l_Array_shrink___main___rarg(x_4, x_2);
x_8 = lean::array_push(x_7, x_6);
x_9 = lean::box(0);
lean::cnstr_set(x_1, 3, x_9);
lean::cnstr_set(x_1, 0, x_8);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_13 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_10);
x_14 = l_Array_shrink___main___rarg(x_10, x_2);
x_15 = lean::array_push(x_14, x_13);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_16);
return x_17;
}
}
}
obj* l_Lean_Parser_ParserState_keepLatest___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParserState_replaceLongest(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_1, x_3);
x_5 = l_Lean_Parser_ParserState_keepLatest(x_4, x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParserState_replaceLongest___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParserState_replaceLongest(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_longestMatchStep___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_10 = lean::array_get_size(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_ParserState_restore(x_6, x_10, x_2);
x_12 = lean::apply_3(x_3, x_4, x_5, x_11);
if (lean::obj_tag(x_7) == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; uint8 x_15; 
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
x_15 = lean::nat_dec_lt(x_8, x_14);
if (x_15 == 0)
{
uint8 x_16; 
lean::dec(x_1);
x_16 = lean::nat_dec_lt(x_14, x_8);
lean::dec(x_14);
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_8);
x_17 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_12, x_10);
return x_17;
}
else
{
obj* x_18; 
x_18 = l_Lean_Parser_ParserState_restore(x_12, x_10, x_8);
lean::dec(x_10);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_14);
lean::dec(x_8);
x_19 = l_Lean_Parser_ParserState_replaceLongest(x_12, x_1, x_10);
lean::dec(x_1);
return x_19;
}
}
else
{
obj* x_20; 
lean::dec(x_13);
lean::dec(x_1);
x_20 = l_Lean_Parser_ParserState_restore(x_12, x_10, x_8);
lean::dec(x_10);
return x_20;
}
}
else
{
obj* x_21; 
x_21 = lean::cnstr_get(x_12, 3);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_7);
x_22 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_12, x_1);
return x_22;
}
else
{
obj* x_23; obj* x_24; uint8 x_25; 
lean::dec(x_21);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_7, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_12, 1);
lean::inc(x_24);
x_25 = lean::nat_dec_lt(x_8, x_24);
if (x_25 == 0)
{
uint8 x_26; 
x_26 = lean::nat_dec_lt(x_24, x_8);
lean::dec(x_24);
if (x_26 == 0)
{
obj* x_27; 
lean::dec(x_8);
lean::dec(x_7);
x_27 = l_Lean_Parser_ParserState_mergeErrors(x_12, x_10, x_23);
lean::dec(x_23);
lean::dec(x_10);
return x_27;
}
else
{
obj* x_28; 
lean::dec(x_23);
x_28 = l_Lean_Parser_ParserState_keepPrevError(x_12, x_10, x_8, x_7);
lean::dec(x_10);
return x_28;
}
}
else
{
obj* x_29; 
lean::dec(x_24);
lean::dec(x_23);
lean::dec(x_8);
lean::dec(x_7);
x_29 = l_Lean_Parser_ParserState_keepNewError(x_12, x_10);
lean::dec(x_10);
return x_29;
}
}
}
}
}
obj* l_Lean_Parser_longestMatchStep(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_longestMatchStep___rarg), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_longestMatchStep___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_longestMatchStep(x_2);
return x_3;
}
}
obj* l_Lean_Parser_longestMatchMkResult(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 3);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_1, x_4);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
if (x_8 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_choiceKind;
x_10 = l_Lean_Parser_ParserState_mkNode(x_2, x_9, x_1);
return x_10;
}
}
else
{
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Lean_Parser_longestMatchFnAux___main(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_8 = l_Lean_Parser_longestMatchMkResult(x_2, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_2);
x_12 = l_Lean_Parser_longestMatchStep___rarg(x_2, x_3, x_11, x_5, x_6, x_7);
x_4 = x_10;
x_7 = x_12;
goto _start;
}
}
}
obj* l_Lean_Parser_longestMatchFnAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = l_Lean_Parser_longestMatchFnAux___main(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_Lean_Parser_longestMatchFnAux(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_longestMatchFnAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_longestMatchFnAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = l_Lean_Parser_longestMatchFnAux(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_Lean_Parser_longestMatchFn_u2081___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::apply_3(x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_7, x_6);
return x_9;
}
else
{
lean::dec(x_8);
lean::dec(x_6);
return x_7;
}
}
}
obj* l_Lean_Parser_longestMatchFn_u2081(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_longestMatchFn_u2081___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_longestMatchFn_u2081___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_longestMatchFn_u2081(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_longestMatchFn___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("longestMatch: empty list");
return x_1;
}
}
obj* l_Lean_Parser_longestMatchFn___main(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_4);
lean::dec(x_3);
x_6 = l_Lean_Parser_longestMatchFn___main___closed__1;
x_7 = l_Lean_Parser_ParserState_mkError(x_5, x_6);
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_Parser_longestMatchFn_u2081___rarg(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
x_14 = lean::array_get_size(x_13);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::dec(x_12);
lean::inc(x_4);
lean::inc(x_3);
x_17 = lean::apply_3(x_16, x_3, x_4, x_5);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
lean::inc(x_14);
x_19 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_17, x_14);
x_20 = l_Lean_Parser_longestMatchFnAux___main(x_1, x_14, x_15, x_8, x_3, x_4, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_18);
x_21 = l_Lean_Parser_ParserState_shrinkStack(x_17, x_14);
x_22 = l_Lean_Parser_longestMatchFnAux___main(x_1, x_14, x_15, x_8, x_3, x_4, x_21);
return x_22;
}
}
}
}
}
obj* l_Lean_Parser_longestMatchFn___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_longestMatchFn___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_longestMatchFn(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_longestMatchFn___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_longestMatchFn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_longestMatchFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_anyOfFn___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("anyOf: empty list");
return x_1;
}
}
obj* l_Lean_Parser_anyOfFn___main(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_4);
lean::dec(x_3);
x_6 = l_Lean_Parser_anyOfFn___main___closed__1;
x_7 = l_Lean_Parser_ParserState_mkError(x_5, x_6);
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_3(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_14 = lean::cnstr_get(x_5, 0);
lean::inc(x_14);
x_15 = lean::array_get_size(x_14);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_5, 1);
lean::inc(x_16);
lean::inc(x_4);
lean::inc(x_3);
x_17 = lean::apply_3(x_13, x_3, x_4, x_5);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_3);
return x_17;
}
else
{
obj* x_19; uint8 x_20; 
lean::dec(x_18);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
x_20 = lean::nat_dec_eq(x_19, x_16);
lean::dec(x_19);
if (x_20 == 0)
{
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_3);
return x_17;
}
else
{
obj* x_21; 
x_21 = l_Lean_Parser_ParserState_restore(x_17, x_15, x_16);
lean::dec(x_15);
x_2 = x_8;
x_5 = x_21;
goto _start;
}
}
}
}
}
}
obj* l_Lean_Parser_anyOfFn___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_anyOfFn___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_anyOfFn(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_anyOfFn___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_anyOfFn___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_anyOfFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_TokenMap_insert___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_1, x_2, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_1, x_2, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_TokenMap_insert(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_TokenMap_insert___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_TokenMap_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Parser_TokenMap_HasEmptyc(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* _init_l_Lean_Parser_currLbp___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("numLit");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_currLbp___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("strLit");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_currLbp(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = l_Lean_Parser_peekToken(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 1);
lean::dec(x_6);
x_7 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_3, 1, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
switch (lean::obj_tag(x_11)) {
case 0:
{
uint8 x_12; 
lean::dec(x_1);
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_3, 1);
lean::dec(x_13);
x_14 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_3, 1, x_14);
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::mk_nat_obj(0u);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
case 1:
{
uint8 x_18; 
lean::dec(x_1);
x_18 = !lean::is_exclusive(x_3);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_19 = lean::cnstr_get(x_3, 1);
lean::dec(x_19);
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_21 = l_Lean_Parser_currLbp___closed__1;
x_22 = lean_name_dec_eq(x_20, x_21);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = l_Lean_Parser_currLbp___closed__2;
x_24 = lean_name_dec_eq(x_20, x_23);
lean::dec(x_20);
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_3, 1, x_25);
return x_3;
}
else
{
obj* x_26; 
x_26 = l_Lean_Parser_maxPrec;
lean::cnstr_set(x_3, 1, x_26);
return x_3;
}
}
else
{
obj* x_27; 
lean::dec(x_20);
x_27 = l_Lean_Parser_maxPrec;
lean::cnstr_set(x_3, 1, x_27);
return x_3;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; uint8 x_31; 
x_28 = lean::cnstr_get(x_3, 0);
lean::inc(x_28);
lean::dec(x_3);
x_29 = lean::cnstr_get(x_11, 0);
lean::inc(x_29);
lean::dec(x_11);
x_30 = l_Lean_Parser_currLbp___closed__1;
x_31 = lean_name_dec_eq(x_29, x_30);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = l_Lean_Parser_currLbp___closed__2;
x_33 = lean_name_dec_eq(x_29, x_32);
lean::dec(x_29);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::mk_nat_obj(0u);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_36; obj* x_37; 
x_36 = l_Lean_Parser_maxPrec;
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_29);
x_38 = l_Lean_Parser_maxPrec;
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_28);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
case 2:
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; 
x_40 = lean::cnstr_get(x_3, 0);
lean::inc(x_40);
lean::dec(x_3);
x_41 = lean::cnstr_get(x_11, 1);
lean::inc(x_41);
lean::dec(x_11);
x_42 = lean::cnstr_get(x_1, 4);
lean::inc(x_42);
lean::dec(x_1);
x_43 = lean::mk_nat_obj(0u);
x_44 = l_Lean_Parser_Trie_matchPrefix___rarg(x_41, x_42, x_43);
lean::dec(x_41);
x_45 = !lean::is_exclusive(x_44);
if (x_45 == 0)
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_44, 1);
x_47 = lean::cnstr_get(x_44, 0);
lean::dec(x_47);
if (lean::obj_tag(x_46) == 0)
{
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set(x_44, 0, x_40);
return x_44;
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_46, 0);
lean::inc(x_48);
lean::dec(x_46);
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set(x_44, 0, x_40);
return x_44;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
lean::dec(x_49);
lean::cnstr_set(x_44, 1, x_50);
lean::cnstr_set(x_44, 0, x_40);
return x_44;
}
}
}
else
{
obj* x_51; 
x_51 = lean::cnstr_get(x_44, 1);
lean::inc(x_51);
lean::dec(x_44);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; 
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_40);
lean::cnstr_set(x_52, 1, x_43);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = lean::cnstr_get(x_51, 0);
lean::inc(x_53);
lean::dec(x_51);
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; 
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_40);
lean::cnstr_set(x_55, 1, x_43);
return x_55;
}
else
{
obj* x_56; obj* x_57; 
x_56 = lean::cnstr_get(x_54, 0);
lean::inc(x_56);
lean::dec(x_54);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_40);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
}
default: 
{
uint8 x_58; 
lean::dec(x_11);
lean::dec(x_1);
x_58 = !lean::is_exclusive(x_3);
if (x_58 == 0)
{
obj* x_59; obj* x_60; 
x_59 = lean::cnstr_get(x_3, 1);
lean::dec(x_59);
x_60 = l_Lean_Parser_maxPrec;
lean::cnstr_set(x_3, 1, x_60);
return x_3;
}
else
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = lean::cnstr_get(x_3, 0);
lean::inc(x_61);
lean::dec(x_3);
x_62 = l_Lean_Parser_maxPrec;
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_indexed___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("ident");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_indexed___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_Lean_Parser_peekToken(x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_7 = x_4;
} else {
 lean::dec_ref(x_4);
 x_7 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_7);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; obj* x_19; 
lean::dec(x_7);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_5);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
case 1:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_8 = x_20;
goto block_14;
}
case 2:
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
lean::dec(x_17);
x_22 = lean::box(0);
x_23 = lean_name_mk_string(x_22, x_21);
x_8 = x_23;
goto block_14;
}
default: 
{
obj* x_24; 
lean::dec(x_17);
x_24 = l_Lean_Parser_indexed___rarg___closed__1;
x_8 = x_24;
goto block_14;
}
}
}
block_14:
{
obj* x_9; 
x_9 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_Lean_Parser_indexed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_indexed___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_indexed___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_indexed___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parser_6__mkResult(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_2, x_5);
x_7 = lean::nat_dec_eq(x_4, x_6);
lean::dec(x_6);
lean::dec(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_nullKind;
x_9 = l_Lean_Parser_ParserState_mkNode(x_1, x_8, x_2);
return x_9;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* _init_l_Lean_Parser_leadingParser___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected ");
return x_1;
}
}
obj* l_Lean_Parser_leadingParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_9 = l_Lean_Parser_indexed___rarg(x_8, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = l_List_isEmpty___main___rarg(x_11);
if (x_12 == 0)
{
uint8 x_13; obj* x_14; obj* x_15; 
x_13 = 0;
x_14 = l_Lean_Parser_longestMatchFn___main(x_13, x_11, x_3, x_4, x_10);
x_15 = l___private_init_lean_parser_parser_6__mkResult(x_14, x_7);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
x_16 = l_Lean_Parser_leadingParser___closed__1;
x_17 = lean::string_append(x_16, x_1);
x_18 = l_Lean_Parser_ParserState_mkError(x_10, x_17);
return x_18;
}
}
}
obj* l_Lean_Parser_leadingParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_trailingParser___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expected trail of ");
return x_1;
}
}
obj* l_Lean_Parser_trailingParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::inc(x_4);
x_9 = l_Lean_Parser_indexed___rarg(x_8, x_4, x_5);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = l_List_isEmpty___main___rarg(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_15 = lean::array_get_size(x_14);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
x_17 = 1;
lean::inc(x_4);
lean::inc(x_3);
x_18 = l_Lean_Parser_longestMatchFn___main(x_17, x_11, x_3, x_4, x_10);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; 
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_3);
x_20 = l___private_init_lean_parser_parser_6__mkResult(x_18, x_7);
return x_20;
}
else
{
obj* x_21; uint8 x_22; 
lean::dec(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
x_22 = lean::nat_dec_eq(x_21, x_16);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_23; 
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_3);
x_23 = l___private_init_lean_parser_parser_6__mkResult(x_18, x_7);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_Lean_Parser_ParserState_restore(x_18, x_15, x_16);
lean::dec(x_15);
x_25 = l_Lean_Parser_anyOfFn___main(x_17, x_13, x_3, x_4, x_24);
x_26 = l___private_init_lean_parser_parser_6__mkResult(x_25, x_7);
return x_26;
}
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_27 = l_Lean_Parser_trailingParser___closed__1;
x_28 = lean::string_append(x_27, x_1);
x_29 = l_Lean_Parser_ParserState_mkError(x_10, x_28);
return x_29;
}
}
}
obj* l_Lean_Parser_trailingParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_trailingParser(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_trailingLoop___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
lean::inc(x_4);
x_7 = l_Lean_Parser_currLbp(x_4, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::nat_dec_le(x_9, x_3);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_4);
lean::inc(x_2);
x_11 = l_Lean_Parser_trailingParser(x_1, x_2, x_5, x_4, x_8);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_13);
lean::dec(x_13);
x_15 = l_Lean_Parser_ParserState_popSyntax(x_11);
x_5 = x_14;
x_6 = x_15;
goto _start;
}
else
{
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_2);
return x_11;
}
}
else
{
obj* x_17; 
lean::dec(x_4);
lean::dec(x_2);
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_8, x_5);
return x_17;
}
}
}
obj* l_Lean_Parser_trailingLoop___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_trailingLoop(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_trailingLoop___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_trailingLoop(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_prattParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_4);
lean::inc(x_3);
x_6 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_11 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_9, x_10);
lean::dec(x_3);
return x_11;
}
else
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
}
obj* l_Lean_Parser_prattParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_prattParser(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_mkParserContext(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_Lean_FileMap_ofString(x_2);
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_5);
lean::cnstr_set(x_6, 4, x_4);
return x_6;
}
}
obj* l_Lean_Parser_mkParserState(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
x_3 = lean::box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
return x_6;
}
}
obj* l_Lean_Parser_mkParserState___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_mkParserState(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_runParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_2, 3);
lean::inc(x_6);
lean::inc(x_3);
x_7 = l_Lean_Parser_mkParserContext(x_1, x_3, x_4, x_6);
x_8 = l_Lean_Parser_mkParserState(x_3);
lean::dec(x_3);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_10 = l_Lean_Parser_prattParser(x_5, x_2, x_9, x_7, x_8);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_7);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
x_13 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_12);
lean::dec(x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_11);
x_15 = l_Lean_Parser_ParserState_toErrorMsg(x_7, x_10);
lean::dec(x_10);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
}
obj* l_Lean_Parser_runParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_runParser(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_mkBuiltinParsingTablesRef___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = l_Lean_Parser_Trie_empty(lean::box(0));
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
return x_4;
}
}
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkBuiltinParsingTablesRef___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_parser_7__updateTokens(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
x_10 = lean::apply_1(x_4, x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; uint8 x_12; 
lean::free_heap_obj(x_1);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_11);
return x_3;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::dec(x_3);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
else
{
obj* x_16; uint8 x_17; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_17 = !lean::is_exclusive(x_3);
if (x_17 == 0)
{
obj* x_18; 
x_18 = lean::cnstr_get(x_3, 0);
lean::dec(x_18);
lean::cnstr_set(x_1, 3, x_16);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::dec(x_3);
lean::cnstr_set(x_1, 3, x_16);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_1, 0);
x_22 = lean::cnstr_get(x_1, 1);
x_23 = lean::cnstr_get(x_1, 2);
x_24 = lean::cnstr_get(x_1, 3);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_1);
x_25 = lean::apply_1(x_4, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_23);
lean::dec(x_22);
lean::dec(x_21);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_27 = lean::cnstr_get(x_3, 1);
lean::inc(x_27);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_28 = x_3;
} else {
 lean::dec_ref(x_3);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
 lean::cnstr_set_tag(x_29, 1);
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_25, 0);
lean::inc(x_30);
lean::dec(x_25);
x_31 = lean::cnstr_get(x_3, 1);
lean::inc(x_31);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_32 = x_3;
} else {
 lean::dec_ref(x_3);
 x_32 = lean::box(0);
}
x_33 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_33, 0, x_21);
lean::cnstr_set(x_33, 1, x_22);
lean::cnstr_set(x_33, 2, x_23);
lean::cnstr_set(x_33, 3, x_30);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
}
obj* l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::box(0);
x_10 = lean_name_mk_string(x_9, x_8);
lean::inc(x_1);
x_11 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_10, x_1);
lean::cnstr_set(x_2, 0, x_11);
x_3 = x_5;
goto _start;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
x_15 = lean::cnstr_get(x_2, 2);
x_16 = lean::cnstr_get(x_2, 3);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_18 = lean::box(0);
x_19 = lean_name_mk_string(x_18, x_17);
lean::inc(x_1);
x_20 = l_Lean_Parser_TokenMap_insert___rarg(x_13, x_19, x_1);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_16);
x_2 = x_21;
x_3 = x_5;
goto _start;
}
}
}
}
obj* _init_l_Lean_Parser_addBuiltinLeadingParser___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid builtin parser '");
return x_1;
}
}
obj* _init_l_Lean_Parser_addBuiltinLeadingParser___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("', initial token is not statically known");
return x_1;
}
}
obj* l_Lean_Parser_addBuiltinLeadingParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::io_ref_get(x_1, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = lean::io_ref_reset(x_1, x_5);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
lean::dec(x_11);
lean::cnstr_set(x_9, 0, x_8);
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
lean::inc(x_12);
x_13 = l___private_init_lean_parser_parser_7__updateTokens(x_7, x_12, x_9);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
lean::dec(x_12);
switch (lean::obj_tag(x_14)) {
case 0:
{
uint8 x_15; 
lean::dec(x_3);
x_15 = !lean::is_exclusive(x_13);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_13, 0);
lean::dec(x_16);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_2);
x_19 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_20 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_21 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_22 = lean::string_append(x_20, x_21);
lean::cnstr_set_tag(x_13, 1);
lean::cnstr_set(x_13, 0, x_22);
return x_13;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_13, 1);
lean::inc(x_23);
lean::dec(x_13);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_2);
x_26 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_27 = lean::string_append(x_26, x_25);
lean::dec(x_25);
x_28 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_29 = lean::string_append(x_27, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_23);
return x_30;
}
}
case 1:
{
uint8 x_31; 
lean::dec(x_3);
x_31 = !lean::is_exclusive(x_13);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_13, 0);
lean::dec(x_32);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_2);
x_35 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_37 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_38 = lean::string_append(x_36, x_37);
lean::cnstr_set_tag(x_13, 1);
lean::cnstr_set(x_13, 0, x_38);
return x_13;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_39 = lean::cnstr_get(x_13, 1);
lean::inc(x_39);
lean::dec(x_13);
x_40 = l_Lean_Name_toString___closed__1;
x_41 = l_Lean_Name_toStringWithSep___main(x_40, x_2);
x_42 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_43 = lean::string_append(x_42, x_41);
lean::dec(x_41);
x_44 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_45 = lean::string_append(x_43, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_39);
return x_46;
}
}
default: 
{
uint8 x_47; 
lean::dec(x_2);
x_47 = !lean::is_exclusive(x_13);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_13, 0);
x_49 = lean::cnstr_get(x_14, 0);
lean::inc(x_49);
lean::dec(x_14);
lean::cnstr_set(x_13, 0, x_8);
x_50 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_3, x_48, x_49);
x_51 = lean::io_ref_set(x_1, x_50, x_13);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_13, 0);
x_53 = lean::cnstr_get(x_13, 1);
lean::inc(x_53);
lean::inc(x_52);
lean::dec(x_13);
x_54 = lean::cnstr_get(x_14, 0);
lean::inc(x_54);
lean::dec(x_14);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_8);
lean::cnstr_set(x_55, 1, x_53);
x_56 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_3, x_52, x_54);
x_57 = lean::io_ref_set(x_1, x_56, x_55);
return x_57;
}
}
}
}
else
{
uint8 x_58; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_2);
x_58 = !lean::is_exclusive(x_13);
if (x_58 == 0)
{
return x_13;
}
else
{
obj* x_59; obj* x_60; obj* x_61; 
x_59 = lean::cnstr_get(x_13, 0);
x_60 = lean::cnstr_get(x_13, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_13);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_9, 1);
lean::inc(x_62);
lean::dec(x_9);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_8);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::cnstr_get(x_3, 0);
lean::inc(x_64);
lean::inc(x_64);
x_65 = l___private_init_lean_parser_parser_7__updateTokens(x_7, x_64, x_63);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; 
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
lean::dec(x_64);
switch (lean::obj_tag(x_66)) {
case 0:
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_3);
x_67 = lean::cnstr_get(x_65, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_68 = x_65;
} else {
 lean::dec_ref(x_65);
 x_68 = lean::box(0);
}
x_69 = l_Lean_Name_toString___closed__1;
x_70 = l_Lean_Name_toStringWithSep___main(x_69, x_2);
x_71 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_72 = lean::string_append(x_71, x_70);
lean::dec(x_70);
x_73 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_74 = lean::string_append(x_72, x_73);
if (lean::is_scalar(x_68)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_68;
 lean::cnstr_set_tag(x_75, 1);
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_67);
return x_75;
}
case 1:
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_3);
x_76 = lean::cnstr_get(x_65, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_77 = x_65;
} else {
 lean::dec_ref(x_65);
 x_77 = lean::box(0);
}
x_78 = l_Lean_Name_toString___closed__1;
x_79 = l_Lean_Name_toStringWithSep___main(x_78, x_2);
x_80 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_81 = lean::string_append(x_80, x_79);
lean::dec(x_79);
x_82 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_83 = lean::string_append(x_81, x_82);
if (lean::is_scalar(x_77)) {
 x_84 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_84 = x_77;
 lean::cnstr_set_tag(x_84, 1);
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_76);
return x_84;
}
default: 
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_2);
x_85 = lean::cnstr_get(x_65, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_65, 1);
lean::inc(x_86);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_87 = x_65;
} else {
 lean::dec_ref(x_65);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_66, 0);
lean::inc(x_88);
lean::dec(x_66);
if (lean::is_scalar(x_87)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_87;
}
lean::cnstr_set(x_89, 0, x_8);
lean::cnstr_set(x_89, 1, x_86);
x_90 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_3, x_85, x_88);
x_91 = lean::io_ref_set(x_1, x_90, x_89);
return x_91;
}
}
}
else
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_64);
lean::dec(x_3);
lean::dec(x_2);
x_92 = lean::cnstr_get(x_65, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_65, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_94 = x_65;
} else {
 lean::dec_ref(x_65);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8 x_96; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_96 = !lean::is_exclusive(x_9);
if (x_96 == 0)
{
return x_9;
}
else
{
obj* x_97; obj* x_98; obj* x_99; 
x_97 = lean::cnstr_get(x_9, 0);
x_98 = lean::cnstr_get(x_9, 1);
lean::inc(x_98);
lean::inc(x_97);
lean::dec(x_9);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_100 = lean::cnstr_get(x_5, 0);
x_101 = lean::cnstr_get(x_5, 1);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_5);
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_101);
x_104 = lean::io_ref_reset(x_1, x_103);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_106 = x_104;
} else {
 lean::dec_ref(x_104);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_102);
lean::cnstr_set(x_107, 1, x_105);
x_108 = lean::cnstr_get(x_3, 0);
lean::inc(x_108);
lean::inc(x_108);
x_109 = l___private_init_lean_parser_parser_7__updateTokens(x_100, x_108, x_107);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; 
x_110 = lean::cnstr_get(x_108, 1);
lean::inc(x_110);
lean::dec(x_108);
switch (lean::obj_tag(x_110)) {
case 0:
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_3);
x_111 = lean::cnstr_get(x_109, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_112 = x_109;
} else {
 lean::dec_ref(x_109);
 x_112 = lean::box(0);
}
x_113 = l_Lean_Name_toString___closed__1;
x_114 = l_Lean_Name_toStringWithSep___main(x_113, x_2);
x_115 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_116 = lean::string_append(x_115, x_114);
lean::dec(x_114);
x_117 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_118 = lean::string_append(x_116, x_117);
if (lean::is_scalar(x_112)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_112;
 lean::cnstr_set_tag(x_119, 1);
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_111);
return x_119;
}
case 1:
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_3);
x_120 = lean::cnstr_get(x_109, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_121 = x_109;
} else {
 lean::dec_ref(x_109);
 x_121 = lean::box(0);
}
x_122 = l_Lean_Name_toString___closed__1;
x_123 = l_Lean_Name_toStringWithSep___main(x_122, x_2);
x_124 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_125 = lean::string_append(x_124, x_123);
lean::dec(x_123);
x_126 = l_Lean_Parser_addBuiltinLeadingParser___closed__2;
x_127 = lean::string_append(x_125, x_126);
if (lean::is_scalar(x_121)) {
 x_128 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_128 = x_121;
 lean::cnstr_set_tag(x_128, 1);
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_120);
return x_128;
}
default: 
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_2);
x_129 = lean::cnstr_get(x_109, 0);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_109, 1);
lean::inc(x_130);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_131 = x_109;
} else {
 lean::dec_ref(x_109);
 x_131 = lean::box(0);
}
x_132 = lean::cnstr_get(x_110, 0);
lean::inc(x_132);
lean::dec(x_110);
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_102);
lean::cnstr_set(x_133, 1, x_130);
x_134 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_3, x_129, x_132);
x_135 = lean::io_ref_set(x_1, x_134, x_133);
return x_135;
}
}
}
else
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_108);
lean::dec(x_3);
lean::dec(x_2);
x_136 = lean::cnstr_get(x_109, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_109, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_138 = x_109;
} else {
 lean::dec_ref(x_109);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_136);
lean::cnstr_set(x_139, 1, x_137);
return x_139;
}
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_100);
lean::dec(x_3);
lean::dec(x_2);
x_140 = lean::cnstr_get(x_104, 0);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_104, 1);
lean::inc(x_141);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_142 = x_104;
} else {
 lean::dec_ref(x_104);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_140);
lean::cnstr_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
uint8 x_144; 
lean::dec(x_3);
lean::dec(x_2);
x_144 = !lean::is_exclusive(x_5);
if (x_144 == 0)
{
return x_5;
}
else
{
obj* x_145; obj* x_146; obj* x_147; 
x_145 = lean::cnstr_get(x_5, 0);
x_146 = lean::cnstr_get(x_5, 1);
lean::inc(x_146);
lean::inc(x_145);
lean::dec(x_5);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_146);
return x_147;
}
}
}
}
obj* l_Lean_Parser_addBuiltinLeadingParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_2, 1);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::box(0);
x_10 = lean_name_mk_string(x_9, x_8);
lean::inc(x_1);
x_11 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_10, x_1);
lean::cnstr_set(x_2, 1, x_11);
x_3 = x_5;
goto _start;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
x_15 = lean::cnstr_get(x_2, 2);
x_16 = lean::cnstr_get(x_2, 3);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_18 = lean::box(0);
x_19 = lean_name_mk_string(x_18, x_17);
lean::inc(x_1);
x_20 = l_Lean_Parser_TokenMap_insert___rarg(x_14, x_19, x_1);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_16);
x_2 = x_21;
x_3 = x_5;
goto _start;
}
}
}
}
obj* l_Lean_Parser_addBuiltinTrailingParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::io_ref_get(x_1, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = lean::io_ref_reset(x_1, x_5);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
lean::dec(x_11);
lean::cnstr_set(x_9, 0, x_8);
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
lean::inc(x_12);
x_13 = l___private_init_lean_parser_parser_7__updateTokens(x_7, x_12, x_9);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::cnstr_set(x_13, 0, x_8);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::dec(x_12);
switch (lean::obj_tag(x_16)) {
case 0:
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_15, 2);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set(x_15, 2, x_19);
x_20 = lean::io_ref_set(x_1, x_15, x_13);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_15, 0);
x_22 = lean::cnstr_get(x_15, 1);
x_23 = lean::cnstr_get(x_15, 2);
x_24 = lean::cnstr_get(x_15, 3);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_15);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_21);
lean::cnstr_set(x_26, 1, x_22);
lean::cnstr_set(x_26, 2, x_25);
lean::cnstr_set(x_26, 3, x_24);
x_27 = lean::io_ref_set(x_1, x_26, x_13);
return x_27;
}
}
case 1:
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_15);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_15, 2);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_29);
lean::cnstr_set(x_15, 2, x_30);
x_31 = lean::io_ref_set(x_1, x_15, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_15, 0);
x_33 = lean::cnstr_get(x_15, 1);
x_34 = lean::cnstr_get(x_15, 2);
x_35 = lean::cnstr_get(x_15, 3);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_15);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_3);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_32);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_36);
lean::cnstr_set(x_37, 3, x_35);
x_38 = lean::io_ref_set(x_1, x_37, x_13);
return x_38;
}
}
default: 
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_16, 0);
lean::inc(x_39);
lean::dec(x_16);
x_40 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_15, x_39);
x_41 = lean::io_ref_set(x_1, x_40, x_13);
return x_41;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_13, 0);
x_43 = lean::cnstr_get(x_13, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_13);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_8);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::cnstr_get(x_12, 1);
lean::inc(x_45);
lean::dec(x_12);
switch (lean::obj_tag(x_45)) {
case 0:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_46 = lean::cnstr_get(x_42, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_42, 2);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_42, 3);
lean::inc(x_49);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 lean::cnstr_release(x_42, 2);
 lean::cnstr_release(x_42, 3);
 x_50 = x_42;
} else {
 lean::dec_ref(x_42);
 x_50 = lean::box(0);
}
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_3);
lean::cnstr_set(x_51, 1, x_48);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_46);
lean::cnstr_set(x_52, 1, x_47);
lean::cnstr_set(x_52, 2, x_51);
lean::cnstr_set(x_52, 3, x_49);
x_53 = lean::io_ref_set(x_1, x_52, x_44);
return x_53;
}
case 1:
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = lean::cnstr_get(x_42, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_42, 1);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_42, 2);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_42, 3);
lean::inc(x_57);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 lean::cnstr_release(x_42, 2);
 lean::cnstr_release(x_42, 3);
 x_58 = x_42;
} else {
 lean::dec_ref(x_42);
 x_58 = lean::box(0);
}
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_3);
lean::cnstr_set(x_59, 1, x_56);
if (lean::is_scalar(x_58)) {
 x_60 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_60 = x_58;
}
lean::cnstr_set(x_60, 0, x_54);
lean::cnstr_set(x_60, 1, x_55);
lean::cnstr_set(x_60, 2, x_59);
lean::cnstr_set(x_60, 3, x_57);
x_61 = lean::io_ref_set(x_1, x_60, x_44);
return x_61;
}
default: 
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = lean::cnstr_get(x_45, 0);
lean::inc(x_62);
lean::dec(x_45);
x_63 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_42, x_62);
x_64 = lean::io_ref_set(x_1, x_63, x_44);
return x_64;
}
}
}
}
else
{
uint8 x_65; 
lean::dec(x_12);
lean::dec(x_3);
x_65 = !lean::is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
obj* x_66; obj* x_67; obj* x_68; 
x_66 = lean::cnstr_get(x_13, 0);
x_67 = lean::cnstr_get(x_13, 1);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_13);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_69 = lean::cnstr_get(x_9, 1);
lean::inc(x_69);
lean::dec(x_9);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_8);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::cnstr_get(x_3, 0);
lean::inc(x_71);
lean::inc(x_71);
x_72 = l___private_init_lean_parser_parser_7__updateTokens(x_7, x_71, x_70);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_75 = x_72;
} else {
 lean::dec_ref(x_72);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_8);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::cnstr_get(x_71, 1);
lean::inc(x_77);
lean::dec(x_71);
switch (lean::obj_tag(x_77)) {
case 0:
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_78 = lean::cnstr_get(x_73, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_73, 1);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_73, 2);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_73, 3);
lean::inc(x_81);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 lean::cnstr_release(x_73, 2);
 lean::cnstr_release(x_73, 3);
 x_82 = x_73;
} else {
 lean::dec_ref(x_73);
 x_82 = lean::box(0);
}
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_3);
lean::cnstr_set(x_83, 1, x_80);
if (lean::is_scalar(x_82)) {
 x_84 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_84 = x_82;
}
lean::cnstr_set(x_84, 0, x_78);
lean::cnstr_set(x_84, 1, x_79);
lean::cnstr_set(x_84, 2, x_83);
lean::cnstr_set(x_84, 3, x_81);
x_85 = lean::io_ref_set(x_1, x_84, x_76);
return x_85;
}
case 1:
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_86 = lean::cnstr_get(x_73, 0);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_73, 1);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_73, 2);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_73, 3);
lean::inc(x_89);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 lean::cnstr_release(x_73, 2);
 lean::cnstr_release(x_73, 3);
 x_90 = x_73;
} else {
 lean::dec_ref(x_73);
 x_90 = lean::box(0);
}
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_3);
lean::cnstr_set(x_91, 1, x_88);
if (lean::is_scalar(x_90)) {
 x_92 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_92 = x_90;
}
lean::cnstr_set(x_92, 0, x_86);
lean::cnstr_set(x_92, 1, x_87);
lean::cnstr_set(x_92, 2, x_91);
lean::cnstr_set(x_92, 3, x_89);
x_93 = lean::io_ref_set(x_1, x_92, x_76);
return x_93;
}
default: 
{
obj* x_94; obj* x_95; obj* x_96; 
x_94 = lean::cnstr_get(x_77, 0);
lean::inc(x_94);
lean::dec(x_77);
x_95 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_73, x_94);
x_96 = lean::io_ref_set(x_1, x_95, x_76);
return x_96;
}
}
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_71);
lean::dec(x_3);
x_97 = lean::cnstr_get(x_72, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_72, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_99 = x_72;
} else {
 lean::dec_ref(x_72);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
lean::cnstr_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
uint8 x_101; 
lean::dec(x_7);
lean::dec(x_3);
x_101 = !lean::is_exclusive(x_9);
if (x_101 == 0)
{
return x_9;
}
else
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_9, 0);
x_103 = lean::cnstr_get(x_9, 1);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_9);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_105 = lean::cnstr_get(x_5, 0);
x_106 = lean::cnstr_get(x_5, 1);
lean::inc(x_106);
lean::inc(x_105);
lean::dec(x_5);
x_107 = lean::box(0);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_106);
x_109 = lean::io_ref_reset(x_1, x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_110 = lean::cnstr_get(x_109, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_111 = x_109;
} else {
 lean::dec_ref(x_109);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_107);
lean::cnstr_set(x_112, 1, x_110);
x_113 = lean::cnstr_get(x_3, 0);
lean::inc(x_113);
lean::inc(x_113);
x_114 = l___private_init_lean_parser_parser_7__updateTokens(x_105, x_113, x_112);
if (lean::obj_tag(x_114) == 0)
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_114, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 lean::cnstr_release(x_114, 1);
 x_117 = x_114;
} else {
 lean::dec_ref(x_114);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_107);
lean::cnstr_set(x_118, 1, x_116);
x_119 = lean::cnstr_get(x_113, 1);
lean::inc(x_119);
lean::dec(x_113);
switch (lean::obj_tag(x_119)) {
case 0:
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_120 = lean::cnstr_get(x_115, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_115, 1);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_115, 2);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_115, 3);
lean::inc(x_123);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 lean::cnstr_release(x_115, 2);
 lean::cnstr_release(x_115, 3);
 x_124 = x_115;
} else {
 lean::dec_ref(x_115);
 x_124 = lean::box(0);
}
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_3);
lean::cnstr_set(x_125, 1, x_122);
if (lean::is_scalar(x_124)) {
 x_126 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_126 = x_124;
}
lean::cnstr_set(x_126, 0, x_120);
lean::cnstr_set(x_126, 1, x_121);
lean::cnstr_set(x_126, 2, x_125);
lean::cnstr_set(x_126, 3, x_123);
x_127 = lean::io_ref_set(x_1, x_126, x_118);
return x_127;
}
case 1:
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_128 = lean::cnstr_get(x_115, 0);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_115, 1);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_115, 2);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_115, 3);
lean::inc(x_131);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 lean::cnstr_release(x_115, 2);
 lean::cnstr_release(x_115, 3);
 x_132 = x_115;
} else {
 lean::dec_ref(x_115);
 x_132 = lean::box(0);
}
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_3);
lean::cnstr_set(x_133, 1, x_130);
if (lean::is_scalar(x_132)) {
 x_134 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_134 = x_132;
}
lean::cnstr_set(x_134, 0, x_128);
lean::cnstr_set(x_134, 1, x_129);
lean::cnstr_set(x_134, 2, x_133);
lean::cnstr_set(x_134, 3, x_131);
x_135 = lean::io_ref_set(x_1, x_134, x_118);
return x_135;
}
default: 
{
obj* x_136; obj* x_137; obj* x_138; 
x_136 = lean::cnstr_get(x_119, 0);
lean::inc(x_136);
lean::dec(x_119);
x_137 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_115, x_136);
x_138 = lean::io_ref_set(x_1, x_137, x_118);
return x_138;
}
}
}
else
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_113);
lean::dec(x_3);
x_139 = lean::cnstr_get(x_114, 0);
lean::inc(x_139);
x_140 = lean::cnstr_get(x_114, 1);
lean::inc(x_140);
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 lean::cnstr_release(x_114, 1);
 x_141 = x_114;
} else {
 lean::dec_ref(x_114);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_139);
lean::cnstr_set(x_142, 1, x_140);
return x_142;
}
}
else
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_105);
lean::dec(x_3);
x_143 = lean::cnstr_get(x_109, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_109, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_145 = x_109;
} else {
 lean::dec_ref(x_109);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_143);
lean::cnstr_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
uint8 x_147; 
lean::dec(x_3);
x_147 = !lean::is_exclusive(x_5);
if (x_147 == 0)
{
return x_5;
}
else
{
obj* x_148; obj* x_149; obj* x_150; 
x_148 = lean::cnstr_get(x_5, 0);
x_149 = lean::cnstr_get(x_5, 1);
lean::inc(x_149);
lean::inc(x_148);
lean::dec(x_5);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_148);
lean::cnstr_set(x_150, 1, x_149);
return x_150;
}
}
}
}
obj* l_Lean_Parser_addBuiltinTrailingParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_2, 0);
lean::dec(x_5);
lean::inc(x_4);
lean::cnstr_set_tag(x_2, 1);
lean::cnstr_set(x_2, 0, x_4);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_2, 0);
lean::dec(x_11);
lean::inc(x_10);
lean::cnstr_set(x_2, 0, x_10);
return x_2;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* _init_l_Lean_Parser_declareBuiltinParser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_regBuiltinParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_declareBuiltinParser___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("IO");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_3, x_4);
x_6 = lean::mk_string("Unit");
x_7 = lean_name_mk_string(x_1, x_6);
x_8 = lean_expr_mk_const(x_7, x_4);
x_9 = lean_expr_mk_app(x_5, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_declareBuiltinParser___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to emit registration code for builtin parser '");
return x_1;
}
}
obj* l_Lean_Parser_declareBuiltinParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_6 = l_Lean_Parser_declareBuiltinParser___closed__1;
lean::inc(x_4);
x_7 = l_Lean_Name_append___main(x_6, x_4);
x_8 = lean::box(0);
x_9 = lean_expr_mk_const(x_3, x_8);
lean::inc(x_4);
x_10 = l_Lean_nameToExprAux___main(x_4);
lean::inc(x_4);
x_11 = lean_expr_mk_const(x_4, x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_mkCApp(x_2, x_14);
x_16 = l_Lean_Parser_declareBuiltinParser___closed__2;
lean::inc(x_7);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_8);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::box(0);
x_19 = 0;
x_20 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_15);
lean::cnstr_set(x_20, 2, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*3, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = l_Lean_Options_empty;
x_23 = lean_add_and_compile(x_1, x_22, x_21);
lean::dec(x_21);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
lean::dec(x_7);
x_24 = !lean::is_exclusive(x_5);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_5, 0);
lean::dec(x_25);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_4);
x_28 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean::string_append(x_29, x_30);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_31);
return x_5;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_5, 1);
lean::inc(x_32);
lean::dec(x_5);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_4);
x_35 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean::string_append(x_36, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_32);
return x_39;
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_4);
x_40 = lean::cnstr_get(x_23, 0);
lean::inc(x_40);
lean::dec(x_23);
x_41 = l_Lean_initAttr;
x_42 = lean::box(0);
x_43 = l_Lean_ParametricAttribute_setParam___rarg(x_41, x_40, x_7, x_42);
x_44 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_43, x_5);
lean::dec(x_43);
return x_44;
}
}
}
obj* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_declareBuiltinParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("addBuiltinLeadingParser");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_declareLeadingBuiltinParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Parser_declareLeadingBuiltinParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_declareLeadingBuiltinParser(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("addBuiltinTrailingParser");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_declareTrailingBuiltinParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Parser_declareTrailingBuiltinParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_declareTrailingBuiltinParser(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown declaration");
return x_1;
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected parser type at '");
return x_1;
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' (`Parser` or `TrailingParser` expected");
return x_1;
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("TrailingParser");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
lean::inc(x_4);
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("ParserKind");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("leading");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6, obj* x_7) {
_start:
{
uint8 x_8; 
x_8 = l_Lean_Syntax_isMissing___main(x_5);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_7, 0);
lean::dec(x_10);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_1);
x_13 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_15 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_16 = lean::string_append(x_14, x_15);
lean::cnstr_set_tag(x_7, 1);
lean::cnstr_set(x_7, 0, x_16);
return x_7;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_7, 1);
lean::inc(x_17);
lean::dec(x_7);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_22 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_23 = lean::string_append(x_21, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
}
else
{
if (x_6 == 0)
{
uint8 x_25; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_25 = !lean::is_exclusive(x_7);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_7, 0);
lean::dec(x_26);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_31 = l_Lean_registerTagAttribute___lambda__5___closed__3;
x_32 = lean::string_append(x_30, x_31);
lean::cnstr_set_tag(x_7, 1);
lean::cnstr_set(x_7, 0, x_32);
return x_7;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_33 = lean::cnstr_get(x_7, 1);
lean::inc(x_33);
lean::dec(x_7);
x_34 = l_Lean_Name_toString___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_1);
x_36 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_37 = lean::string_append(x_36, x_35);
lean::dec(x_35);
x_38 = l_Lean_registerTagAttribute___lambda__5___closed__3;
x_39 = lean::string_append(x_37, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_33);
return x_40;
}
}
else
{
uint8 x_41; 
lean::dec(x_1);
x_41 = !lean::is_exclusive(x_7);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_7, 1);
x_43 = lean::cnstr_get(x_7, 0);
lean::dec(x_43);
x_44 = lean::box(0);
lean::inc(x_42);
lean::cnstr_set(x_7, 0, x_44);
lean::inc(x_4);
lean::inc(x_3);
x_45 = lean::environment_find_core(x_3, x_4);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_46 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1;
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
lean::dec(x_45);
x_49 = l_Lean_ConstantInfo_type(x_48);
lean::dec(x_48);
switch (lean::obj_tag(x_49)) {
case 4:
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
lean::dec(x_49);
x_51 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4;
x_52 = lean_name_dec_eq(x_50, x_51);
lean::dec(x_50);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_53 = l_Lean_Name_toString___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_4);
x_55 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_57 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_58 = lean::string_append(x_56, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_42);
return x_59;
}
else
{
obj* x_60; 
lean::dec(x_42);
x_60 = l_Lean_Parser_declareTrailingBuiltinParser(x_3, x_2, x_4, x_7);
lean::dec(x_3);
return x_60;
}
}
case 5:
{
obj* x_61; 
x_61 = lean::cnstr_get(x_49, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 4)
{
obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_62 = lean::cnstr_get(x_49, 1);
lean::inc(x_62);
lean::dec(x_49);
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
lean::dec(x_61);
x_64 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5;
x_65 = lean_name_dec_eq(x_63, x_64);
lean::dec(x_63);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_62);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_66 = l_Lean_Name_toString___closed__1;
x_67 = l_Lean_Name_toStringWithSep___main(x_66, x_4);
x_68 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_69 = lean::string_append(x_68, x_67);
lean::dec(x_67);
x_70 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_71 = lean::string_append(x_69, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_42);
return x_72;
}
else
{
if (lean::obj_tag(x_62) == 4)
{
obj* x_73; obj* x_74; uint8 x_75; 
x_73 = lean::cnstr_get(x_62, 0);
lean::inc(x_73);
lean::dec(x_62);
x_74 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6;
x_75 = lean_name_dec_eq(x_73, x_74);
lean::dec(x_73);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_76 = l_Lean_Name_toString___closed__1;
x_77 = l_Lean_Name_toStringWithSep___main(x_76, x_4);
x_78 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_79 = lean::string_append(x_78, x_77);
lean::dec(x_77);
x_80 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_81 = lean::string_append(x_79, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_42);
return x_82;
}
else
{
obj* x_83; 
lean::dec(x_42);
x_83 = l_Lean_Parser_declareLeadingBuiltinParser(x_3, x_2, x_4, x_7);
lean::dec(x_3);
return x_83;
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_62);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_84 = l_Lean_Name_toString___closed__1;
x_85 = l_Lean_Name_toStringWithSep___main(x_84, x_4);
x_86 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_87 = lean::string_append(x_86, x_85);
lean::dec(x_85);
x_88 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_89 = lean::string_append(x_87, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_42);
return x_90;
}
}
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_61);
lean::dec(x_49);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_91 = l_Lean_Name_toString___closed__1;
x_92 = l_Lean_Name_toStringWithSep___main(x_91, x_4);
x_93 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_94 = lean::string_append(x_93, x_92);
lean::dec(x_92);
x_95 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_96 = lean::string_append(x_94, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_42);
return x_97;
}
}
default: 
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_49);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_98 = l_Lean_Name_toString___closed__1;
x_99 = l_Lean_Name_toStringWithSep___main(x_98, x_4);
x_100 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_101 = lean::string_append(x_100, x_99);
lean::dec(x_99);
x_102 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_103 = lean::string_append(x_101, x_102);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_42);
return x_104;
}
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_105 = lean::cnstr_get(x_7, 1);
lean::inc(x_105);
lean::dec(x_7);
x_106 = lean::box(0);
lean::inc(x_105);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_105);
lean::inc(x_4);
lean::inc(x_3);
x_108 = lean::environment_find_core(x_3, x_4);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_110; 
lean::dec(x_107);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_109 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1;
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_105);
return x_110;
}
else
{
obj* x_111; obj* x_112; 
x_111 = lean::cnstr_get(x_108, 0);
lean::inc(x_111);
lean::dec(x_108);
x_112 = l_Lean_ConstantInfo_type(x_111);
lean::dec(x_111);
switch (lean::obj_tag(x_112)) {
case 4:
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
lean::dec(x_112);
x_114 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4;
x_115 = lean_name_dec_eq(x_113, x_114);
lean::dec(x_113);
if (x_115 == 0)
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
lean::dec(x_107);
lean::dec(x_3);
lean::dec(x_2);
x_116 = l_Lean_Name_toString___closed__1;
x_117 = l_Lean_Name_toStringWithSep___main(x_116, x_4);
x_118 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_119 = lean::string_append(x_118, x_117);
lean::dec(x_117);
x_120 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_121 = lean::string_append(x_119, x_120);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_105);
return x_122;
}
else
{
obj* x_123; 
lean::dec(x_105);
x_123 = l_Lean_Parser_declareTrailingBuiltinParser(x_3, x_2, x_4, x_107);
lean::dec(x_3);
return x_123;
}
}
case 5:
{
obj* x_124; 
x_124 = lean::cnstr_get(x_112, 0);
lean::inc(x_124);
if (lean::obj_tag(x_124) == 4)
{
obj* x_125; obj* x_126; obj* x_127; uint8 x_128; 
x_125 = lean::cnstr_get(x_112, 1);
lean::inc(x_125);
lean::dec(x_112);
x_126 = lean::cnstr_get(x_124, 0);
lean::inc(x_126);
lean::dec(x_124);
x_127 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5;
x_128 = lean_name_dec_eq(x_126, x_127);
lean::dec(x_126);
if (x_128 == 0)
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_125);
lean::dec(x_107);
lean::dec(x_3);
lean::dec(x_2);
x_129 = l_Lean_Name_toString___closed__1;
x_130 = l_Lean_Name_toStringWithSep___main(x_129, x_4);
x_131 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_132 = lean::string_append(x_131, x_130);
lean::dec(x_130);
x_133 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_134 = lean::string_append(x_132, x_133);
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_134);
lean::cnstr_set(x_135, 1, x_105);
return x_135;
}
else
{
if (lean::obj_tag(x_125) == 4)
{
obj* x_136; obj* x_137; uint8 x_138; 
x_136 = lean::cnstr_get(x_125, 0);
lean::inc(x_136);
lean::dec(x_125);
x_137 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6;
x_138 = lean_name_dec_eq(x_136, x_137);
lean::dec(x_136);
if (x_138 == 0)
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_107);
lean::dec(x_3);
lean::dec(x_2);
x_139 = l_Lean_Name_toString___closed__1;
x_140 = l_Lean_Name_toStringWithSep___main(x_139, x_4);
x_141 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_142 = lean::string_append(x_141, x_140);
lean::dec(x_140);
x_143 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_144 = lean::string_append(x_142, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_105);
return x_145;
}
else
{
obj* x_146; 
lean::dec(x_105);
x_146 = l_Lean_Parser_declareLeadingBuiltinParser(x_3, x_2, x_4, x_107);
lean::dec(x_3);
return x_146;
}
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_125);
lean::dec(x_107);
lean::dec(x_3);
lean::dec(x_2);
x_147 = l_Lean_Name_toString___closed__1;
x_148 = l_Lean_Name_toStringWithSep___main(x_147, x_4);
x_149 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_150 = lean::string_append(x_149, x_148);
lean::dec(x_148);
x_151 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_152 = lean::string_append(x_150, x_151);
x_153 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_105);
return x_153;
}
}
}
else
{
obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_124);
lean::dec(x_112);
lean::dec(x_107);
lean::dec(x_3);
lean::dec(x_2);
x_154 = l_Lean_Name_toString___closed__1;
x_155 = l_Lean_Name_toStringWithSep___main(x_154, x_4);
x_156 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_157 = lean::string_append(x_156, x_155);
lean::dec(x_155);
x_158 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_159 = lean::string_append(x_157, x_158);
x_160 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_105);
return x_160;
}
}
default: 
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_112);
lean::dec(x_107);
lean::dec(x_3);
lean::dec(x_2);
x_161 = l_Lean_Name_toString___closed__1;
x_162 = l_Lean_Name_toStringWithSep___main(x_161, x_4);
x_163 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_164 = lean::string_append(x_163, x_162);
lean::dec(x_162);
x_165 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_166 = lean::string_append(x_164, x_165);
x_167 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_105);
return x_167;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Builtin parser");
return x_1;
}
}
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed), 7, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_5, 0, x_1);
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_8 = l_Lean_registerTagAttribute___closed__5;
x_9 = l_Lean_registerTagAttribute___closed__6;
x_10 = 1;
x_11 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_4);
lean::cnstr_set(x_11, 3, x_5);
lean::cnstr_set(x_11, 4, x_6);
lean::cnstr_set(x_11, 5, x_8);
lean::cnstr_set(x_11, 6, x_9);
lean::cnstr_set(x_11, 7, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*8, x_10);
x_12 = l_Lean_registerAttribute(x_11, x_3);
return x_12;
}
}
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_6);
lean::dec(x_6);
x_9 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean::dec(x_5);
return x_9;
}
}
obj* _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinCommandParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("builtinCommandParsingTable");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_regBuiltinCommandParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__1;
x_3 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__2;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
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
obj* _init_l_Lean_Parser_runBuiltinParserUnsafe___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to access builtin reference");
return x_1;
}
}
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_11; obj* x_12; 
x_11 = l_unsafeIO___rarg___closed__1;
x_12 = lean::io_ref_get(x_2, x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
lean::inc(x_5);
x_14 = l_Lean_Parser_prattParser(x_1, x_13, x_3, x_4, x_5);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_6 = x_15;
goto block_10;
}
else
{
obj* x_16; 
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
x_16 = lean::box(0);
x_6 = x_16;
goto block_10;
}
block_10:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_runBuiltinParserUnsafe___closed__1;
x_8 = l_Lean_Parser_ParserState_mkError(x_5, x_7);
return x_8;
}
else
{
obj* x_9; 
lean::dec(x_5);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
return x_9;
}
}
}
}
obj* l_Lean_Parser_runBuiltinParserUnsafe___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_runBuiltinParserUnsafe(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_runBuiltinParser___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Parser_runBuiltinParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_runBuiltinParser___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_Lean_Parser_runBuiltinParser___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_runBuiltinParser___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_runBuiltinParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_runBuiltinParser(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_Parser_commandParser___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("command");
return x_1;
}
}
obj* l_Lean_Parser_commandParser___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_commandParser___elambda__1___closed__1;
x_6 = l_Lean_Parser_builtinCommandParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_commandParser(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_commandParser___elambda__1___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_Parser_inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_commandParser___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_commandParser___elambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_termParser___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term");
return x_1;
}
}
obj* l_Lean_Parser_termParser___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_termParser___elambda__1___closed__1;
x_6 = l_Lean_Parser_builtinTermParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_termParser(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser___elambda__1___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_Parser_inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_termParser___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_termParser___elambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_regBuiltinTestParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinTestParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinTestParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("builtinTestParsingTable");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_regBuiltinTestParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinTestParserAttr___closed__1;
x_3 = l_Lean_Parser_regBuiltinTestParserAttr___closed__2;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_testParser___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("testExpr");
return x_1;
}
}
obj* l_Lean_Parser_testParser___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_testParser___elambda__1___closed__1;
x_6 = l_Lean_Parser_builtinTestParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_testParser(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_testParser___elambda__1___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_Parser_inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_testParser___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_testParser___elambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* initialize_init_lean_position(obj*);
obj* initialize_init_lean_syntax(obj*);
obj* initialize_init_lean_toexpr(obj*);
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_attributes(obj*);
obj* initialize_init_lean_parser_trie(obj*);
obj* initialize_init_lean_parser_identifier(obj*);
obj* initialize_init_lean_compiler_initattr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_parser(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_position(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_syntax(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_toexpr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_trie(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_identifier(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_initattr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
lean::mark_persistent(l_Lean_Parser_maxPrec);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "maxPrec"), l_Lean_Parser_maxPrec);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenConfig"), "beq"), 2, l_Lean_Parser_TokenConfig_beq___boxed);
l_Lean_Parser_TokenConfig_HasBeq = _init_l_Lean_Parser_TokenConfig_HasBeq();
lean::mark_persistent(l_Lean_Parser_TokenConfig_HasBeq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenConfig"), "HasBeq"), l_Lean_Parser_TokenConfig_HasBeq);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "initCacheForInput"), 1, l_Lean_Parser_initCacheForInput___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "hasError"), 1, l_Lean_Parser_ParserState_hasError___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "stackSize"), 1, l_Lean_Parser_ParserState_stackSize___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "restore"), 3, l_Lean_Parser_ParserState_restore___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "setPos"), 2, l_Lean_Parser_ParserState_setPos);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "setCache"), 2, l_Lean_Parser_ParserState_setCache);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "pushSyntax"), 2, l_Lean_Parser_ParserState_pushSyntax);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "popSyntax"), 1, l_Lean_Parser_ParserState_popSyntax);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "shrinkStack"), 2, l_Lean_Parser_ParserState_shrinkStack___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "next"), 3, l_Lean_Parser_ParserState_next___boxed);
l_Lean_Parser_ParserState_toErrorMsg___closed__1 = _init_l_Lean_Parser_ParserState_toErrorMsg___closed__1();
lean::mark_persistent(l_Lean_Parser_ParserState_toErrorMsg___closed__1);
l_Lean_Parser_ParserState_toErrorMsg___closed__2 = _init_l_Lean_Parser_ParserState_toErrorMsg___closed__2();
lean::mark_persistent(l_Lean_Parser_ParserState_toErrorMsg___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "toErrorMsg"), 2, l_Lean_Parser_ParserState_toErrorMsg___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "mkNode"), 3, l_Lean_Parser_ParserState_mkNode);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "mkError"), 2, l_Lean_Parser_ParserState_mkError);
l_Lean_Parser_ParserState_mkEOIError___closed__1 = _init_l_Lean_Parser_ParserState_mkEOIError___closed__1();
lean::mark_persistent(l_Lean_Parser_ParserState_mkEOIError___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "mkEOIError"), 1, l_Lean_Parser_ParserState_mkEOIError);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "mkErrorAt"), 3, l_Lean_Parser_ParserState_mkErrorAt);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserFn"), "inhabited"), 3, l_Lean_Parser_ParserFn_inhabited___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "FirstTokens"), "merge"), 2, l_Lean_Parser_FirstTokens_merge);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "FirstTokens"), "seq"), 2, l_Lean_Parser_FirstTokens_seq___boxed);
l_Lean_Parser_Parser_inhabited___closed__1 = _init_l_Lean_Parser_Parser_inhabited___closed__1();
lean::mark_persistent(l_Lean_Parser_Parser_inhabited___closed__1);
l_Lean_Parser_Parser_inhabited___closed__2 = _init_l_Lean_Parser_Parser_inhabited___closed__2();
lean::mark_persistent(l_Lean_Parser_Parser_inhabited___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Parser"), "inhabited"), 1, l_Lean_Parser_Parser_inhabited___boxed);
l_Lean_Parser_epsilonInfo = _init_l_Lean_Parser_epsilonInfo();
lean::mark_persistent(l_Lean_Parser_epsilonInfo);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "epsilonInfo"), l_Lean_Parser_epsilonInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "pushLeadingFn"), 3, l_Lean_Parser_pushLeadingFn___boxed);
l_Lean_Parser_pushLeading = _init_l_Lean_Parser_pushLeading();
lean::mark_persistent(l_Lean_Parser_pushLeading);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "pushLeading"), l_Lean_Parser_pushLeading);
l_Lean_Parser_checkLeadingFn___closed__1 = _init_l_Lean_Parser_checkLeadingFn___closed__1();
lean::mark_persistent(l_Lean_Parser_checkLeadingFn___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "checkLeadingFn"), 4, l_Lean_Parser_checkLeadingFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "checkLeading"), 1, l_Lean_Parser_checkLeading);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "andthenAux"), 4, l_Lean_Parser_andthenAux);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "andthenFn"), 1, l_Lean_Parser_andthenFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "andthenInfo"), 2, l_Lean_Parser_andthenInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "andthen"), 3, l_Lean_Parser_andthen___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "nodeFn"), 1, l_Lean_Parser_nodeFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "nodeInfo"), 1, l_Lean_Parser_nodeInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "node"), 3, l_Lean_Parser_node___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "orelseFn"), 1, l_Lean_Parser_orelseFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "orelseInfo"), 2, l_Lean_Parser_orelseInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "orelse"), 3, l_Lean_Parser_orelse___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "noFirstTokenInfo"), 1, l_Lean_Parser_noFirstTokenInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "tryFn"), 1, l_Lean_Parser_tryFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "try"), 2, l_Lean_Parser_try___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "optionalFn"), 1, l_Lean_Parser_optionalFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "optional"), 2, l_Lean_Parser_optional___boxed);
l_Lean_Parser_manyAux___main___closed__1 = _init_l_Lean_Parser_manyAux___main___closed__1();
lean::mark_persistent(l_Lean_Parser_manyAux___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "manyAux"), 5, l_Lean_Parser_manyAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "manyFn"), 5, l_Lean_Parser_manyFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "many"), 2, l_Lean_Parser_many___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "many1"), 2, l_Lean_Parser_many1___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "sepByFn"), 7, l_Lean_Parser_sepByFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "sepBy1Fn"), 7, l_Lean_Parser_sepBy1Fn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "sepByInfo"), 2, l_Lean_Parser_sepByInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "sepBy1Info"), 2, l_Lean_Parser_sepBy1Info);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "sepBy"), 4, l_Lean_Parser_sepBy___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "sepBy1"), 4, l_Lean_Parser_sepBy1___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "satisfyFn"), 4, l_Lean_Parser_satisfyFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "takeUntilFn"), 3, l_Lean_Parser_takeUntilFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "takeWhileFn"), 3, l_Lean_Parser_takeWhileFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "takeWhile1Fn"), 4, l_Lean_Parser_takeWhile1Fn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "finishCommentBlock"), 3, l_Lean_Parser_finishCommentBlock___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "whitespace"), 2, l_Lean_Parser_whitespace___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkEmptySubstringAt"), 2, l_Lean_Parser_mkEmptySubstringAt);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "rawFn"), 1, l_Lean_Parser_rawFn___boxed);
l_Lean_Parser_hexDigitFn___main___closed__1 = _init_l_Lean_Parser_hexDigitFn___main___closed__1();
lean::mark_persistent(l_Lean_Parser_hexDigitFn___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "hexDigitFn"), 2, l_Lean_Parser_hexDigitFn___boxed);
l_Lean_Parser_quotedCharFn___main___closed__1 = _init_l_Lean_Parser_quotedCharFn___main___closed__1();
lean::mark_persistent(l_Lean_Parser_quotedCharFn___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "quotedCharFn"), 2, l_Lean_Parser_quotedCharFn___boxed);
l_Lean_Parser_strLitKind = _init_l_Lean_Parser_strLitKind();
lean::mark_persistent(l_Lean_Parser_strLitKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLitKind"), l_Lean_Parser_strLitKind);
l_Lean_Parser_numLitKind = _init_l_Lean_Parser_numLitKind();
lean::mark_persistent(l_Lean_Parser_numLitKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "numLitKind"), l_Lean_Parser_numLitKind);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkNodeToken"), 4, l_Lean_Parser_mkNodeToken___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLitFnAux"), 3, l_Lean_Parser_strLitFnAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "decimalNumberFn"), 3, l_Lean_Parser_decimalNumberFn___boxed);
l_Lean_Parser_binNumberFn___closed__1 = _init_l_Lean_Parser_binNumberFn___closed__1();
lean::mark_persistent(l_Lean_Parser_binNumberFn___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "binNumberFn"), 3, l_Lean_Parser_binNumberFn___boxed);
l_Lean_Parser_octalNumberFn___closed__1 = _init_l_Lean_Parser_octalNumberFn___closed__1();
lean::mark_persistent(l_Lean_Parser_octalNumberFn___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "octalNumberFn"), 3, l_Lean_Parser_octalNumberFn___boxed);
l_Lean_Parser_hexNumberFn___closed__1 = _init_l_Lean_Parser_hexNumberFn___closed__1();
lean::mark_persistent(l_Lean_Parser_hexNumberFn___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "hexNumberFn"), 3, l_Lean_Parser_hexNumberFn___boxed);
l_Lean_Parser_numberFnAux___closed__1 = _init_l_Lean_Parser_numberFnAux___closed__1();
lean::mark_persistent(l_Lean_Parser_numberFnAux___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "numberFnAux"), 2, l_Lean_Parser_numberFnAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "isIdCont"), 2, l_Lean_Parser_isIdCont___boxed);
l_Lean_Parser_mkTokenAndFixPos___closed__1 = _init_l_Lean_Parser_mkTokenAndFixPos___closed__1();
lean::mark_persistent(l_Lean_Parser_mkTokenAndFixPos___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkTokenAndFixPos"), 4, l_Lean_Parser_mkTokenAndFixPos___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkIdResult"), 5, l_Lean_Parser_mkIdResult___boxed);
l_Lean_Parser_identFnAux___main___closed__1 = _init_l_Lean_Parser_identFnAux___main___closed__1();
lean::mark_persistent(l_Lean_Parser_identFnAux___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "identFnAux"), 5, l_Lean_Parser_identFnAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "tokenFn"), 2, l_Lean_Parser_tokenFn);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "peekToken"), 2, l_Lean_Parser_peekToken);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "satisfySymbolFn"), 4, l_Lean_Parser_satisfySymbolFn);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "symbolFnAux"), 4, l_Lean_Parser_symbolFnAux___boxed);
l_Lean_Parser_insertToken___closed__1 = _init_l_Lean_Parser_insertToken___closed__1();
lean::mark_persistent(l_Lean_Parser_insertToken___closed__1);
l_Lean_Parser_insertToken___closed__2 = _init_l_Lean_Parser_insertToken___closed__2();
lean::mark_persistent(l_Lean_Parser_insertToken___closed__2);
l_Lean_Parser_insertToken___closed__3 = _init_l_Lean_Parser_insertToken___closed__3();
lean::mark_persistent(l_Lean_Parser_insertToken___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "insertToken"), 3, l_Lean_Parser_insertToken);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "symbolInfo"), 2, l_Lean_Parser_symbolInfo);
l_Lean_Parser_symbolFn___rarg___closed__1 = _init_l_Lean_Parser_symbolFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_symbolFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "symbolFn"), 1, l_Lean_Parser_symbolFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "symbol"), 3, l_Lean_Parser_symbol___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "unicodeSymbolFnAux"), 5, l_Lean_Parser_unicodeSymbolFnAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "unicodeSymbolInfo"), 3, l_Lean_Parser_unicodeSymbolInfo);
l_Lean_Parser_unicodeSymbolFn___rarg___closed__1 = _init_l_Lean_Parser_unicodeSymbolFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_unicodeSymbolFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "unicodeSymbolFn"), 1, l_Lean_Parser_unicodeSymbolFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "unicodeSymbol"), 4, l_Lean_Parser_unicodeSymbol___boxed);
l_Lean_Parser_mkAtomicInfo___closed__1 = _init_l_Lean_Parser_mkAtomicInfo___closed__1();
lean::mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkAtomicInfo"), 1, l_Lean_Parser_mkAtomicInfo);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "numLitFn"), 2, l_Lean_Parser_numLitFn___boxed);
l_Lean_Parser_numLit___closed__1 = _init_l_Lean_Parser_numLit___closed__1();
lean::mark_persistent(l_Lean_Parser_numLit___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "numLit"), 1, l_Lean_Parser_numLit___boxed);
l_Lean_Parser_strLitFn___rarg___closed__1 = _init_l_Lean_Parser_strLitFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_strLitFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLitFn"), 2, l_Lean_Parser_strLitFn___boxed);
l_Lean_Parser_strLit___closed__1 = _init_l_Lean_Parser_strLit___closed__1();
lean::mark_persistent(l_Lean_Parser_strLit___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLit"), 1, l_Lean_Parser_strLit___boxed);
l_Lean_Parser_identFn___rarg___closed__1 = _init_l_Lean_Parser_identFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_identFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "identFn"), 2, l_Lean_Parser_identFn___boxed);
l_Lean_Parser_ident___closed__1 = _init_l_Lean_Parser_ident___closed__1();
lean::mark_persistent(l_Lean_Parser_ident___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ident"), 1, l_Lean_Parser_ident___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "string2basic"), 2, l_Lean_Parser_string2basic___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "keepNewError"), 2, l_Lean_Parser_ParserState_keepNewError___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "keepPrevError"), 4, l_Lean_Parser_ParserState_keepPrevError___boxed);
l_Lean_Parser_ParserState_mergeErrors___closed__1 = _init_l_Lean_Parser_ParserState_mergeErrors___closed__1();
lean::mark_persistent(l_Lean_Parser_ParserState_mergeErrors___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "mergeErrors"), 3, l_Lean_Parser_ParserState_mergeErrors___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "mkLongestNodeAlt"), 2, l_Lean_Parser_ParserState_mkLongestNodeAlt);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "keepLatest"), 2, l_Lean_Parser_ParserState_keepLatest___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "ParserState"), "replaceLongest"), 3, l_Lean_Parser_ParserState_replaceLongest___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "longestMatchStep"), 1, l_Lean_Parser_longestMatchStep___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "longestMatchMkResult"), 2, l_Lean_Parser_longestMatchMkResult);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "longestMatchFnAux"), 7, l_Lean_Parser_longestMatchFnAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "longestMatchFn₁"), 1, l_Lean_Parser_longestMatchFn_u2081___boxed);
l_Lean_Parser_longestMatchFn___main___closed__1 = _init_l_Lean_Parser_longestMatchFn___main___closed__1();
lean::mark_persistent(l_Lean_Parser_longestMatchFn___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "longestMatchFn"), 5, l_Lean_Parser_longestMatchFn___boxed);
l_Lean_Parser_anyOfFn___main___closed__1 = _init_l_Lean_Parser_anyOfFn___main___closed__1();
lean::mark_persistent(l_Lean_Parser_anyOfFn___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "anyOfFn"), 5, l_Lean_Parser_anyOfFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenMap"), "insert"), 1, l_Lean_Parser_TokenMap_insert);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenMap"), "Inhabited"), 1, l_Lean_Parser_TokenMap_Inhabited);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenMap"), "HasEmptyc"), 1, l_Lean_Parser_TokenMap_HasEmptyc);
l_Lean_Parser_currLbp___closed__1 = _init_l_Lean_Parser_currLbp___closed__1();
lean::mark_persistent(l_Lean_Parser_currLbp___closed__1);
l_Lean_Parser_currLbp___closed__2 = _init_l_Lean_Parser_currLbp___closed__2();
lean::mark_persistent(l_Lean_Parser_currLbp___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "currLbp"), 2, l_Lean_Parser_currLbp);
l_Lean_Parser_indexed___rarg___closed__1 = _init_l_Lean_Parser_indexed___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_indexed___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "indexed"), 1, l_Lean_Parser_indexed);
l_Lean_Parser_leadingParser___closed__1 = _init_l_Lean_Parser_leadingParser___closed__1();
lean::mark_persistent(l_Lean_Parser_leadingParser___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "leadingParser"), 5, l_Lean_Parser_leadingParser___boxed);
l_Lean_Parser_trailingParser___closed__1 = _init_l_Lean_Parser_trailingParser___closed__1();
lean::mark_persistent(l_Lean_Parser_trailingParser___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "trailingParser"), 5, l_Lean_Parser_trailingParser___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "trailingLoop"), 6, l_Lean_Parser_trailingLoop___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "prattParser"), 5, l_Lean_Parser_prattParser___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkParserContext"), 4, l_Lean_Parser_mkParserContext);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkParserState"), 1, l_Lean_Parser_mkParserState___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "runParser"), 5, l_Lean_Parser_runParser___boxed);
l_Lean_Parser_mkBuiltinParsingTablesRef___closed__1 = _init_l_Lean_Parser_mkBuiltinParsingTablesRef___closed__1();
lean::mark_persistent(l_Lean_Parser_mkBuiltinParsingTablesRef___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkBuiltinParsingTablesRef"), 1, l_Lean_Parser_mkBuiltinParsingTablesRef);
l_Lean_Parser_addBuiltinLeadingParser___closed__1 = _init_l_Lean_Parser_addBuiltinLeadingParser___closed__1();
lean::mark_persistent(l_Lean_Parser_addBuiltinLeadingParser___closed__1);
l_Lean_Parser_addBuiltinLeadingParser___closed__2 = _init_l_Lean_Parser_addBuiltinLeadingParser___closed__2();
lean::mark_persistent(l_Lean_Parser_addBuiltinLeadingParser___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "addBuiltinLeadingParser"), 4, l_Lean_Parser_addBuiltinLeadingParser___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "addBuiltinTrailingParser"), 4, l_Lean_Parser_addBuiltinTrailingParser___boxed);
l_Lean_Parser_declareBuiltinParser___closed__1 = _init_l_Lean_Parser_declareBuiltinParser___closed__1();
lean::mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__1);
l_Lean_Parser_declareBuiltinParser___closed__2 = _init_l_Lean_Parser_declareBuiltinParser___closed__2();
lean::mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__2);
l_Lean_Parser_declareBuiltinParser___closed__3 = _init_l_Lean_Parser_declareBuiltinParser___closed__3();
lean::mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "declareBuiltinParser"), 5, l_Lean_Parser_declareBuiltinParser___boxed);
l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1();
lean::mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "declareLeadingBuiltinParser"), 4, l_Lean_Parser_declareLeadingBuiltinParser___boxed);
l_Lean_Parser_declareTrailingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1();
lean::mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "declareTrailingBuiltinParser"), 4, l_Lean_Parser_declareTrailingBuiltinParser___boxed);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6);
l_Lean_Parser_registerBuiltinParserAttribute___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "registerBuiltinParserAttribute"), 3, l_Lean_Parser_registerBuiltinParserAttribute);
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinCommandParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinCommandParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinCommandParsingTable"), l_Lean_Parser_builtinCommandParsingTable);
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinTermParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinTermParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinTermParsingTable"), l_Lean_Parser_builtinTermParsingTable);
l_Lean_Parser_regBuiltinCommandParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinCommandParserAttr___closed__1);
l_Lean_Parser_regBuiltinCommandParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinCommandParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinCommandParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_regBuiltinTermParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__1);
l_Lean_Parser_regBuiltinTermParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTermParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinTermParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinTermParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_runBuiltinParserUnsafe___closed__1 = _init_l_Lean_Parser_runBuiltinParserUnsafe___closed__1();
lean::mark_persistent(l_Lean_Parser_runBuiltinParserUnsafe___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "runBuiltinParserUnsafe"), 5, l_Lean_Parser_runBuiltinParserUnsafe___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "runBuiltinParser"), 4, l_Lean_Parser_runBuiltinParser___boxed);
l_Lean_Parser_commandParser___elambda__1___closed__1 = _init_l_Lean_Parser_commandParser___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_commandParser___elambda__1___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "commandParser"), 1, l_Lean_Parser_commandParser);
l_Lean_Parser_termParser___elambda__1___closed__1 = _init_l_Lean_Parser_termParser___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_termParser___elambda__1___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "termParser"), 1, l_Lean_Parser_termParser);
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinTestParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinTestParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinTestParsingTable"), l_Lean_Parser_builtinTestParsingTable);
l_Lean_Parser_regBuiltinTestParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinTestParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinTestParserAttr___closed__1);
l_Lean_Parser_regBuiltinTestParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinTestParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinTestParserAttr___closed__2);
w = l_Lean_Parser_regBuiltinTestParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_testParser___elambda__1___closed__1 = _init_l_Lean_Parser_testParser___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_testParser___elambda__1___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "testParser"), 1, l_Lean_Parser_testParser);
return w;
}
