// Lean compiler output
// Module: init.lean.parser.parser
// Imports: init.lean.position init.lean.syntax init.lean.environment init.lean.attributes init.lean.evalconst init.lean.parser.trie init.lean.parser.identifier
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
obj* l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3(obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_Parser_checkLeadingFn___closed__1;
obj* l_Lean_Parser_runParser(obj*, obj*, obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn(obj*, obj*, obj*);
obj* l_Lean_Parser_builtinLevelParserAttr;
obj* l_Lean_Parser_unicodeSymbolFnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe(obj*, obj*);
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
obj* l_Lean_Parser_sepBy1(uint8, obj*, obj*, uint8);
obj* l_Lean_AttributeImpl_inhabited___lambda__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFnAux(uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Lean_evalConst___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited___rarg(obj*);
obj* l_Lean_Parser_andthenFn___boxed(obj*);
obj* l_Lean_Parser_epsilonInfo___elambda__1(obj*);
obj* l_Lean_FileMap_toPosition___main(obj*, obj*);
obj* l_Lean_Parser_tryFn___main(uint8);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_TokenConfig_beq___boxed(obj*, obj*);
obj* l_Lean_Parser_whitespace___main(obj*, obj*);
uint8 l_Lean_isIdRest(uint32);
obj* l_Lean_Parser_sepBy1Fn___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_6__mkResult(obj*, obj*);
extern obj* l_Lean_stxInh;
obj* l_Lean_Parser_numberFn___boxed(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
obj* l_Lean_Parser_orelseFn(uint8);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main(uint8, obj*, obj*, uint8, obj*, uint8, obj*, obj*, obj*);
uint8 l_Lean_isIdEndEscape(uint32);
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_anyOfFn___main___closed__1;
obj* l_Lean_Parser_anyOfFn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchMkResult(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_Parser_andthenFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_hasError___boxed(obj*);
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_mkBuiltinTestParserAttr___closed__1;
obj* l_Lean_Parser_decimalNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_BuiltinParserAttribute_getTables___rarg(obj*);
obj* l___private_init_lean_parser_parser_9__updateTokens___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_sepByFn___main(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_leadingParser___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tryFn___main___boxed(obj*);
obj* l_Lean_Parser_currLbp___closed__1;
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_mkTokenAndFixPos___closed__1;
obj* l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(obj*, obj*, obj*);
extern obj* l_Lean_registerTagAttribute___lambda__5___closed__1;
obj* l_Lean_Parser_sepBy1Info___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main(obj*, obj*, obj*);
obj* l_Lean_Parser_hexDigitFn___main___boxed(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3___boxed(obj*, obj*);
obj* l_Lean_Parser_strLitFnAux___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_many1___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_mkNumberKind___closed__1;
obj* l_Lean_Parser_mkParserContext(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_stackSize(obj*);
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
obj* l_Lean_Parser_hexDigitFn___main(obj*, obj*);
obj* l_Lean_Parser_ParserState_toErrorMsg___boxed(obj*, obj*);
obj* l_Lean_Parser_mkStrLitKind(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux(uint8, obj*, obj*, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_mkNodeToken___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_builtinTestParserAttr;
obj* l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___boxed(obj*, obj*);
obj* l_Lean_Parser_ParserState_keepLatest(obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___main(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawFn___boxed(obj*);
obj* l_Lean_Parser_tryFn___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(obj*, obj*);
obj* l_Lean_Parser_ParserState_toErrorMsg___closed__2;
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Parser_hexDigitFn___boxed(obj*, obj*);
obj* l_Lean_Parser_string2basic___boxed(obj*, obj*);
obj* l_Lean_Parser_TokenMap_insert___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_4__tokenFnAux___main(obj*, obj*);
obj* l_Lean_Parser_rawFn___main___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited(uint8);
obj* l_Lean_Parser_unicodeSymbolFn(uint8);
uint8 l_Lean_Parser_TokenConfig_beq___main(obj*, obj*);
obj* l_Lean_Parser_ParserState_mergeErrors___boxed(obj*, obj*, obj*);
uint8 l_Lean_Syntax_isOfKind___main(obj*, obj*);
obj* l_Lean_Parser_longestMatchFn___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_3__isToken___boxed(obj*);
obj* l_Lean_Parser_strLitFn___rarg___closed__1;
obj* l_Lean_Parser_symbolFnAux___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1;
obj* l_Lean_Parser_identFnAux___main___closed__1;
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_8__throwUnexpectedParserType(obj*, obj*);
obj* l_Lean_Parser_quotedCharFn___main___boxed(obj*, obj*);
obj* l_Lean_Parser_optional___boxed(obj*, obj*);
obj* l_Lean_Parser_isIdCont___boxed(obj*, obj*);
obj* l_Lean_Parser_numberFn___rarg(obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*);
obj* l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2;
obj* l_Lean_Parser_checkLeadingFn(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_11__addBuiltinParser___boxed(obj*, obj*, obj*);
extern obj* l_Lean_evalConst___rarg___closed__1;
obj* l_Lean_Parser_quotedCharFn(obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___closed__1;
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn___main(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolFn___boxed(obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_currLbp(obj*, obj*);
obj* l_Lean_Parser_strLitFnAux___main___boxed(obj*, obj*, obj*);
obj* l_ExceptT_lift___rarg___lambda__1(obj*);
obj* l_Lean_Parser_unicodeSymbol___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2;
obj* l___private_init_lean_parser_parser_9__updateTokens(obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_identFnAux___main___spec__4(obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(obj*);
obj* l_Lean_Parser_nodeFn___boxed(obj*);
obj* l_Lean_Parser_hexNumberFn___closed__1;
obj* l_Lean_Parser_longestMatchFn___main___closed__1;
obj* l_Lean_Parser_builtinCommandParserAttr;
obj* l_Lean_Parser_nodeFn___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_node___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_optional(uint8, obj*);
obj* l_Lean_Parser_whitespace___main___boxed(obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_Parser_anyOfFn___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mergeErrors(obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___closed__2;
obj* l___private_init_lean_parser_parser_11__addBuiltinParser(obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___rarg(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_FirstTokens_seq___boxed(obj*, obj*);
obj* l_Lean_Parser_strLitFn(uint8, obj*);
obj* l_Lean_Parser_ParserState_replaceLongest(obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3___boxed(obj*, obj*);
obj* l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(obj*);
obj* l_Lean_Parser_trailingLoop___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___boxed(obj*);
obj* l_Lean_Parser_mkBuiltinCommandParserAttr___closed__1;
uint8 l___private_init_lean_parser_parser_3__isToken___rarg(obj*, obj*);
obj* l_Lean_Parser_optionalFn___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_quotedCharFn___boxed(obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*);
obj* l_Lean_Parser_insertToken___closed__1;
obj* l_Lean_Parser_trailingLoop___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1;
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(obj*);
obj* l_Lean_Parser_finishCommentBlock___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_Inhabited(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Parser_mkNodeToken(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_node(uint8, obj*, obj*);
obj* l_Lean_Parser_rawFn___main(uint8);
obj* l_Lean_Parser_andthen___boxed(obj*, obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__5(obj*, obj*);
obj* l_Lean_Parser_nodeFn___main___boxed(obj*);
obj* l_Lean_Parser_ParserState_mkEOIError___closed__1;
obj* l___private_init_lean_parser_parser_2__rawAux___main___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_restore___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1(obj*, obj*, obj*);
obj* l_Array_extract___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_next___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___main(uint8);
obj* l_Lean_Parser_binNumberFn___closed__1;
obj* l___private_init_lean_parser_parser_2__rawAux(uint8);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(obj*, obj*);
obj* l_Lean_Parser_ParserState_mergeErrors___closed__1;
uint8 l_Lean_isIdBeginEscape(uint32);
obj* l_Lean_Parser_mkBuiltinLevelParserAttr(obj*);
obj* l_Lean_Parser_mkEmptySubstringAt(obj*, obj*);
obj* l_Lean_Parser_binNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_TokenConfig_HasBeq;
obj* l_Lean_Parser_manyAux___main___closed__1;
obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l_Lean_Parser_FirstTokens_merge___main(obj*, obj*);
obj* l_Lean_Parser_number(uint8);
obj* l_Lean_Parser_mkBuiltinCommandParserAttr(obj*);
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
obj* l_Lean_Parser_manyFn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol(uint8, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_BuiltinParserAttribute_runParser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4(obj*, obj*);
uint8 l_UInt32_decLe(uint32, uint32);
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe(obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_mkBuiltinLevelParserAttr___closed__1;
obj* l___private_init_lean_parser_parser_2__rawAux___boxed(obj*);
obj* l_Lean_Parser_strLitFnAux___main(obj*, obj*, obj*);
uint8 l_Lean_Parser_isIdCont(obj*, obj*);
extern "C" obj* lean_get_constant_table(obj*);
uint8 l_Lean_Syntax_isIdent___main(obj*);
obj* l_Lean_Parser_ident(uint8);
obj* l_Lean_Parser_tokenFn(obj*, obj*);
obj* l_Lean_Parser_currLbp___closed__2;
extern obj* l_Lean_registerTagAttribute___closed__6;
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_tryFn___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(obj*, obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_nextKind(obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited___rarg___boxed(obj*);
obj* l_Lean_Parser_ParserState_toErrorMsg___closed__1;
uint8 l_Lean_Syntax_isMissing___main(obj*);
obj* l_Lean_Parser_sepByFn(uint8, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace___boxed(obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_orelseFn___main___boxed(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_mkTokenAndFixPos___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyFn(uint8, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1;
obj* l_Lean_Parser_strLit(uint8);
obj* l_Lean_Parser_orelseFn___main(uint8);
obj* l_Lean_Parser_rawFn___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj*, obj*, obj*);
extern obj* l_Lean_choiceKind;
obj* l_Lean_Parser_unicodeSymbolFnAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_octalNumberFn___closed__1;
obj* l_Lean_Parser_rawFn(uint8);
obj* l_Lean_Parser_tryFn___boxed(obj*);
obj* l_Lean_Parser_identFnAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_setPos(obj*, obj*);
obj* l_Lean_Parser_numberFnAux___boxed(obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol___boxed(obj*, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_empty(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Parser_satisfyFn___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_pushLeadingFn(obj*, obj*, obj*);
obj* l_Lean_Parser_Parser_inhabited___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_insert(obj*);
obj* l_Lean_Parser_takeUntilFn___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(obj*, obj*);
obj* l_Lean_Parser_symbolFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_binNumberFn___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_mkBuiltinTermParserAttr___closed__1;
obj* l_Lean_Parser_many1(uint8, obj*);
obj* l_Lean_Parser_trailingLoop___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken___closed__2;
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Lean_Parser_longestMatchFn___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_11__addBuiltinParser___rarg(obj*);
obj* l_Lean_Parser_takeWhile1Fn___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_hexDigitFn___main___closed__1;
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4;
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_Parser_indexed___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn_u2081___boxed(obj*);
obj* l_Lean_Parser_string2basic(uint8, obj*);
obj* l_Lean_Parser_many(uint8, obj*);
obj* l_Lean_Parser_finishCommentBlock___main(obj*, obj*, obj*);
uint8 l_Lean_Parser_TokenConfig_beq(obj*, obj*);
obj* l___private_init_lean_parser_parser_4__tokenFnAux(obj*, obj*);
obj* l_Lean_Parser_runParser___closed__1;
obj* l_Lean_Parser_mkBuiltinTermParserAttr(obj*);
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l_Lean_Parser_builtinTermParserAttr;
extern obj* l_Lean_registerTagAttribute___lambda__5___closed__2;
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_ParserState_keepNewError(obj*, obj*);
obj* l_Lean_Parser_identFnAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_finishCommentBlock___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1;
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(obj*, obj*);
obj* l_Lean_Parser_FirstTokens_merge(obj*, obj*);
obj* l_Lean_Parser_nodeFn(uint8);
obj* l_Lean_Parser_octalNumberFn___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_Lean_Parser_longestMatchStep(uint8);
obj* l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1;
obj* l_Lean_Parser_BuiltinParserAttribute_getTables(obj*);
obj* l_Lean_Parser_checkLeading(obj*);
obj* l_Lean_Parser_optionalFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
obj* l_Lean_Parser_TokenConfig_beq___main___boxed(obj*, obj*);
obj* l_Lean_Parser_sepBy1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFn___boxed(obj*);
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_andthenAux(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_octalNumberFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_pop(obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_Parser_identFnAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_ConstantInfo_type(obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(obj*, obj*);
obj* l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1(obj*, obj*);
obj* l_Lean_Parser_ParserState_mkEOIError(obj*);
obj* l_Lean_Parser_longestMatchFn_u2081___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchFn_u2081(uint8);
obj* l_Lean_Parser_ParserState_setCache(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(obj*);
obj* l_Lean_Parser_BuiltinParserAttribute_getTables___boxed(obj*);
obj* l_Lean_Parser_number___boxed(obj*);
obj* l_Lean_Parser_ParserState_mkError(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7(obj*);
obj* l_Lean_Parser_quotedCharFn___main(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
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
obj* l_Lean_Parser_trailingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_peekToken(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_prattParser(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_3__isToken___rarg___boxed(obj*, obj*);
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
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*);
obj* l_Lean_Parser_satisfyFn___main___at_Lean_Parser_hexNumberFn___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_numberFn(uint8, obj*);
obj* l_Lean_Parser_manyAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_registerTagAttribute___closed__5;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1___boxed(obj*);
obj* l_Lean_Parser_mkStrLitKind___closed__1;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Lean_Parser_nodeFn___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_next(obj*, obj*, obj*);
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
obj* l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_strLit___boxed(obj*);
obj* l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_orelseFn___boxed(obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
obj* l_Lean_Parser_BuiltinParserAttribute_Inhabited;
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
obj* l_Lean_AttributeImpl_inhabited___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawFn___main___boxed(obj*);
obj* l_Lean_Parser_TokenMap_HasEmptyc(obj*);
obj* l_Lean_Parser_longestMatchFnAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_pushLeading;
obj* l_Lean_Parser_tryFn(uint8);
obj* l_Lean_Parser_epsilonInfo;
obj* l_Lean_Parser_ParserState_toErrorMsg(obj*, obj*);
obj* l_Lean_Parser_symbolFn(uint8);
obj* l_Lean_Parser_BuiltinParserAttribute_runParser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_identFn___rarg___closed__1;
obj* l_Lean_Parser_hexNumberFn(obj*, obj*, obj*);
obj* l_Lean_Parser_orelse(uint8, obj*, obj*);
obj* l_Lean_Parser_satisfyFn(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_orelse___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken___closed__3;
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3;
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_FirstTokens_seq___main(obj*, obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(obj*, obj*);
obj* l_Lean_Parser_mkBuiltinTestParserAttr(obj*);
obj* l_Lean_Parser_hexDigitFn(obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_insertToken(obj*, obj*, obj*);
obj* l_Lean_Parser_numberKind;
obj* l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
uint8 l_Lean_isIdFirst(uint32);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(obj*);
obj* l_Lean_Parser_mkTokenAndFixPos(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbolInfo___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_leadingParser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol(uint8, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_rawFn___rarg(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_keepLatest___boxed(obj*, obj*);
obj* l_Lean_FileMap_ofString(obj*);
obj* l_Lean_Parser_isIdCont___main___boxed(obj*, obj*);
obj* l_Lean_Parser_strLitKind;
obj* l_Lean_Parser_sepByFn___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___main___boxed(obj*);
obj* l_Lean_Parser_longestMatchStep___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(obj*, obj*);
obj* l_Lean_Parser_pushLeadingFn___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_trailingLoop(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_mkLongestNodeAlt(obj*, obj*);
obj* l_Lean_Parser_anyOfFn(uint8, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_longestMatchStep___boxed(obj*);
obj* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parser_2__rawAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkNumberKind(obj*);
obj* l___private_init_lean_parser_parser_3__isToken(obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserState_replaceLongest___boxed(obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepByInfo(obj*, obj*);
obj* l_Lean_Parser_longestMatchFnAux___main(uint8, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_orelseInfo___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserFn_inhabited(uint8, obj*, obj*);
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
obj* x_24; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_24 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
lean::dec(x_11);
if (x_6 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::box(0);
x_26 = l_Lean_Parser_ParserState_pushSyntax(x_24, x_25);
x_27 = l_Lean_nullKind;
x_28 = l_Lean_Parser_ParserState_mkNode(x_26, x_27, x_5);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_24, x_29, x_5);
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
obj* _init_l_Lean_Parser_mkStrLitKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("strLit");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkStrLitKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkStrLitKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_mkNumberKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("number");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkNumberKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkNumberKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
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
x_10 = l_Lean_Parser_numberKind;
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
x_15 = l_Lean_Parser_numberKind;
x_16 = l_Lean_Parser_mkNodeToken(x_15, x_1, x_2, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = l_Lean_Parser_ParserState_setPos(x_4, x_12);
x_18 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_2, x_17);
x_19 = l_Lean_Parser_numberKind;
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
x_8 = l_Lean_Parser_numberKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numberKind;
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
x_8 = l_Lean_Parser_numberKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numberKind;
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
x_8 = l_Lean_Parser_numberKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
x_10 = l_Lean_Parser_numberKind;
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
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_2, 2, x_16);
return x_2;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_2);
x_17 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_4);
lean::inc(x_5);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_5);
lean::cnstr_set(x_18, 2, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_5);
lean::cnstr_set(x_20, 2, x_19);
lean::cnstr_set(x_20, 3, x_3);
return x_20;
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
obj* x_6; 
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l___private_init_lean_parser_parser_4__tokenFnAux___main(x_1, x_2);
x_8 = l___private_init_lean_parser_parser_5__updateCache(x_4, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::nat_dec_eq(x_10, x_4);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_9);
x_12 = l___private_init_lean_parser_parser_4__tokenFnAux___main(x_1, x_2);
x_13 = l___private_init_lean_parser_parser_5__updateCache(x_4, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_4);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::dec(x_9);
x_17 = l_Lean_Parser_ParserState_setPos(x_15, x_16);
return x_17;
}
}
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_4);
lean::dec(x_1);
x_18 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_19 = l_Lean_Parser_ParserState_mkError(x_2, x_18);
return x_19;
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
obj* l_Lean_Parser_numberFn___rarg(obj* x_1, obj* x_2) {
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
x_7 = l_Lean_Parser_numberKind;
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
obj* l_Lean_Parser_numberFn(uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numberFn___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_numberFn___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_numberFn(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_number(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_numberFn___boxed), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_number___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_number(x_2);
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
obj* l_Lean_Parser_strLit(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_strLitFn___boxed), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
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
obj* l_Lean_Parser_ident(uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_identFn___boxed), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
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
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_numberKind;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_currLbp___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_strLitKind;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
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
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_3, 1);
lean::dec(x_19);
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_22 = l_Lean_Parser_currLbp___closed__1;
x_23 = lean::nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = l_Lean_Parser_currLbp___closed__2;
x_25 = lean::nat_dec_eq(x_21, x_24);
lean::dec(x_21);
if (x_25 == 0)
{
obj* x_26; 
x_26 = lean::mk_nat_obj(0u);
lean::cnstr_set(x_3, 1, x_26);
return x_3;
}
else
{
obj* x_27; 
x_27 = l_Lean_Parser_maxPrec;
lean::cnstr_set(x_3, 1, x_27);
return x_3;
}
}
else
{
obj* x_28; 
lean::dec(x_21);
x_28 = l_Lean_Parser_maxPrec;
lean::cnstr_set(x_3, 1, x_28);
return x_3;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_11, 0);
lean::inc(x_30);
lean::dec(x_11);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
x_32 = l_Lean_Parser_currLbp___closed__1;
x_33 = lean::nat_dec_eq(x_31, x_32);
if (x_33 == 0)
{
obj* x_34; uint8 x_35; 
x_34 = l_Lean_Parser_currLbp___closed__2;
x_35 = lean::nat_dec_eq(x_31, x_34);
lean::dec(x_31);
if (x_35 == 0)
{
obj* x_36; obj* x_37; 
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_29);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
x_38 = l_Lean_Parser_maxPrec;
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_31);
x_40 = l_Lean_Parser_maxPrec;
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_29);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
case 2:
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_47; 
x_42 = lean::cnstr_get(x_3, 0);
lean::inc(x_42);
lean::dec(x_3);
x_43 = lean::cnstr_get(x_11, 1);
lean::inc(x_43);
lean::dec(x_11);
x_44 = lean::cnstr_get(x_1, 4);
lean::inc(x_44);
lean::dec(x_1);
x_45 = lean::mk_nat_obj(0u);
x_46 = l_Lean_Parser_Trie_matchPrefix___rarg(x_43, x_44, x_45);
lean::dec(x_43);
x_47 = !lean::is_exclusive(x_46);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_46, 1);
x_49 = lean::cnstr_get(x_46, 0);
lean::dec(x_49);
if (lean::obj_tag(x_48) == 0)
{
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set(x_46, 0, x_42);
return x_46;
}
else
{
obj* x_50; obj* x_51; 
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
lean::dec(x_48);
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
if (lean::obj_tag(x_51) == 0)
{
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set(x_46, 0, x_42);
return x_46;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
lean::dec(x_51);
lean::cnstr_set(x_46, 1, x_52);
lean::cnstr_set(x_46, 0, x_42);
return x_46;
}
}
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_46, 1);
lean::inc(x_53);
lean::dec(x_46);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; 
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_42);
lean::cnstr_set(x_54, 1, x_45);
return x_54;
}
else
{
obj* x_55; obj* x_56; 
x_55 = lean::cnstr_get(x_53, 0);
lean::inc(x_55);
lean::dec(x_53);
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; 
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_42);
lean::cnstr_set(x_57, 1, x_45);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
lean::dec(x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_42);
lean::cnstr_set(x_59, 1, x_58);
return x_59;
}
}
}
}
default: 
{
uint8 x_60; 
lean::dec(x_11);
lean::dec(x_1);
x_60 = !lean::is_exclusive(x_3);
if (x_60 == 0)
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_3, 1);
lean::dec(x_61);
x_62 = l_Lean_Parser_maxPrec;
lean::cnstr_set(x_3, 1, x_62);
return x_3;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = lean::cnstr_get(x_3, 0);
lean::inc(x_63);
lean::dec(x_3);
x_64 = l_Lean_Parser_maxPrec;
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
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
obj* l_Lean_Parser_indexed___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_peekToken(x_2, x_3);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 1);
lean::dec(x_7);
x_8 = lean::box(0);
lean::cnstr_set(x_4, 1, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
if (lean::obj_tag(x_12) == 2)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_4);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_4, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::box(0);
x_17 = lean_name_mk_string(x_16, x_15);
x_18 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_17);
lean::dec(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; 
x_19 = lean::box(0);
lean::cnstr_set(x_4, 1, x_19);
return x_4;
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_18, 0);
lean::inc(x_20);
lean::dec(x_18);
lean::cnstr_set(x_4, 1, x_20);
return x_4;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
lean::dec(x_4);
x_22 = lean::cnstr_get(x_12, 1);
lean::inc(x_22);
lean::dec(x_12);
x_23 = lean::box(0);
x_24 = lean_name_mk_string(x_23, x_22);
x_25 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
lean::dec(x_25);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8 x_30; 
lean::dec(x_12);
x_30 = !lean::is_exclusive(x_4);
if (x_30 == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_4, 1);
lean::dec(x_31);
x_32 = lean::box(0);
lean::cnstr_set(x_4, 1, x_32);
return x_4;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_4, 0);
lean::inc(x_33);
lean::dec(x_4);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
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
obj* l_Lean_Parser_leadingParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_8 = l_Lean_Parser_indexed___rarg(x_7, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
x_11 = 0;
x_12 = l_Lean_Parser_longestMatchFn___main(x_11, x_10, x_2, x_3, x_9);
x_13 = l___private_init_lean_parser_parser_6__mkResult(x_12, x_6);
return x_13;
}
}
obj* l_Lean_Parser_leadingParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_trailingParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_3);
x_8 = l_Lean_Parser_indexed___rarg(x_7, x_3, x_4);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_13 = lean::array_get_size(x_12);
lean::dec(x_12);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_15 = 1;
lean::inc(x_3);
lean::inc(x_2);
x_16 = l_Lean_Parser_longestMatchFn___main(x_15, x_10, x_2, x_3, x_9);
x_17 = lean::cnstr_get(x_16, 3);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
x_18 = l___private_init_lean_parser_parser_6__mkResult(x_16, x_6);
return x_18;
}
else
{
obj* x_19; uint8 x_20; 
lean::dec(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
x_20 = lean::nat_dec_eq(x_19, x_14);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_21; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
x_21 = l___private_init_lean_parser_parser_6__mkResult(x_16, x_6);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_Lean_Parser_ParserState_restore(x_16, x_13, x_14);
lean::dec(x_13);
x_23 = l_Lean_Parser_anyOfFn___main(x_15, x_11, x_2, x_3, x_22);
x_24 = l___private_init_lean_parser_parser_6__mkResult(x_23, x_6);
return x_24;
}
}
}
}
obj* l_Lean_Parser_trailingLoop___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
lean::inc(x_3);
x_6 = l_Lean_Parser_currLbp(x_3, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::nat_dec_le(x_8, x_2);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::inc(x_3);
lean::inc(x_1);
x_10 = l_Lean_Parser_trailingParser(x_1, x_4, x_3, x_7);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_12);
lean::dec(x_12);
x_14 = l_Lean_Parser_ParserState_popSyntax(x_10);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
else
{
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_1);
return x_10;
}
}
else
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
}
obj* l_Lean_Parser_trailingLoop___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_trailingLoop(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_trailingLoop___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_trailingLoop(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_prattParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
lean::inc(x_2);
x_5 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_ParserState_popSyntax(x_5);
x_10 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_8, x_9);
lean::dec(x_2);
return x_10;
}
else
{
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
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
obj* _init_l_Lean_Parser_runParser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 3, x_3);
return x_4;
}
}
obj* l_Lean_Parser_runParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 3);
lean::inc(x_5);
x_6 = l_Lean_Parser_mkParserContext(x_1, x_3, x_4, x_5);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Lean_Parser_runParser___closed__1;
lean::inc(x_6);
x_9 = l_Lean_Parser_prattParser(x_2, x_7, x_6, x_8);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_6);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = l_Array_back___at___private_init_lean_parser_parser_5__updateCache___spec__1(x_11);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_10);
x_14 = l_Lean_Parser_ParserState_toErrorMsg(x_6, x_9);
lean::dec(x_9);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
obj* _init_l_Lean_Parser_BuiltinParserAttribute_Inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::mk_string("");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_AttributeImpl_inhabited___lambda__1___boxed), 5, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_AttributeImpl_inhabited___lambda__2___boxed), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_AttributeImpl_inhabited___lambda__3___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_AttributeImpl_inhabited___lambda__4___boxed), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_AttributeImpl_inhabited___lambda__5), 2, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set(x_8, 4, x_5);
lean::cnstr_set(x_8, 5, x_6);
lean::cnstr_set(x_8, 6, x_7);
lean::cnstr_set(x_8, 7, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set(x_10, 3, x_8);
return x_10;
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
obj* _init_l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1() {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = 0;
x_2 = l_Lean_Parser_Parser_inhabited(x_1);
return x_2;
}
}
obj* l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_constant_table(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::array_get_size(x_5);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_8, x_9);
lean::dec(x_8);
x_11 = l_Array_binSearchAux___main___at_Lean_evalConst___spec__1(x_5, x_7, x_6, x_10);
lean::dec(x_7);
lean::dec(x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l_Lean_evalConst___rarg___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean::string_append(x_15, x_16);
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_17);
return x_3;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_20 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1;
x_21 = x_19;
lean::cnstr_set(x_3, 0, x_21);
return x_3;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_3, 0);
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_3);
x_24 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::array_get_size(x_22);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_26, x_27);
lean::dec(x_26);
x_29 = l_Array_binSearchAux___main___at_Lean_evalConst___spec__1(x_22, x_25, x_24, x_28);
lean::dec(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_1);
x_32 = l_Lean_evalConst___rarg___closed__1;
x_33 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean::string_append(x_33, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_23);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_39 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1;
x_40 = x_38;
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_23);
return x_41;
}
}
}
else
{
uint8 x_42; 
lean::dec(x_1);
x_42 = !lean::is_exclusive(x_3);
if (x_42 == 0)
{
return x_3;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_3, 0);
x_44 = lean::cnstr_get(x_3, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_3);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
}
}
obj* l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__2(obj* x_1, obj* x_2, obj* x_3) {
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
obj* _init_l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid parser '");
return x_1;
}
}
obj* _init_l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("', initial token is not statically known");
return x_1;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_8);
x_10 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1(x_8, x_3);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = lean::box(0);
lean::cnstr_set(x_10, 0, x_13);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::inc(x_14);
x_15 = l___private_init_lean_parser_parser_7__updateTokens(x_1, x_14, x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_28; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_18 = x_15;
} else {
 lean::dec_ref(x_15);
 x_18 = lean::box(0);
}
x_28 = lean::cnstr_get(x_14, 1);
lean::inc(x_28);
lean::dec(x_14);
switch (lean::obj_tag(x_28)) {
case 0:
{
lean::dec(x_16);
lean::dec(x_12);
lean::dec(x_9);
x_19 = x_13;
goto block_27;
}
case 1:
{
lean::dec(x_16);
lean::dec(x_12);
lean::dec(x_9);
x_19 = x_13;
goto block_27;
}
default: 
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_18);
lean::dec(x_8);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
lean::dec(x_28);
x_30 = l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__2(x_12, x_16, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_13);
lean::cnstr_set(x_31, 1, x_17);
x_1 = x_30;
x_2 = x_9;
x_3 = x_31;
goto _start;
}
}
block_27:
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
x_20 = l_Lean_Name_toString___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_8);
x_22 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_24 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_25 = lean::string_append(x_23, x_24);
if (lean::is_scalar(x_18)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_18;
 lean::cnstr_set_tag(x_26, 1);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
}
else
{
uint8 x_33; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_9);
lean::dec(x_8);
x_33 = !lean::is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get(x_15, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_15);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_10, 0);
x_38 = lean::cnstr_get(x_10, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_10);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
lean::inc(x_41);
x_42 = l___private_init_lean_parser_parser_7__updateTokens(x_1, x_41, x_40);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_55; 
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_45 = x_42;
} else {
 lean::dec_ref(x_42);
 x_45 = lean::box(0);
}
x_55 = lean::cnstr_get(x_41, 1);
lean::inc(x_55);
lean::dec(x_41);
switch (lean::obj_tag(x_55)) {
case 0:
{
lean::dec(x_43);
lean::dec(x_37);
lean::dec(x_9);
x_46 = x_39;
goto block_54;
}
case 1:
{
lean::dec(x_43);
lean::dec(x_37);
lean::dec(x_9);
x_46 = x_39;
goto block_54;
}
default: 
{
obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_45);
lean::dec(x_8);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
lean::dec(x_55);
x_57 = l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__2(x_37, x_43, x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_39);
lean::cnstr_set(x_58, 1, x_44);
x_1 = x_57;
x_2 = x_9;
x_3 = x_58;
goto _start;
}
}
block_54:
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_46);
x_47 = l_Lean_Name_toString___closed__1;
x_48 = l_Lean_Name_toStringWithSep___main(x_47, x_8);
x_49 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_50 = lean::string_append(x_49, x_48);
lean::dec(x_48);
x_51 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_52 = lean::string_append(x_50, x_51);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_45;
 lean::cnstr_set_tag(x_53, 1);
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_44);
return x_53;
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_41);
lean::dec(x_37);
lean::dec(x_9);
lean::dec(x_8);
x_60 = lean::cnstr_get(x_42, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_42, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_62 = x_42;
} else {
 lean::dec_ref(x_42);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
uint8 x_64; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_1);
x_64 = !lean::is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::cnstr_get(x_10, 0);
x_66 = lean::cnstr_get(x_10, 1);
lean::inc(x_66);
lean::inc(x_65);
lean::dec(x_10);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
obj* _init_l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1() {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = 1;
x_2 = l_Lean_Parser_Parser_inhabited(x_1);
return x_2;
}
}
obj* l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_constant_table(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::array_get_size(x_5);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_8, x_9);
lean::dec(x_8);
x_11 = l_Array_binSearchAux___main___at_Lean_evalConst___spec__1(x_5, x_7, x_6, x_10);
lean::dec(x_7);
lean::dec(x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l_Lean_evalConst___rarg___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean::string_append(x_15, x_16);
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_17);
return x_3;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_20 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1;
x_21 = x_19;
lean::cnstr_set(x_3, 0, x_21);
return x_3;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_3, 0);
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_3);
x_24 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::array_get_size(x_22);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_26, x_27);
lean::dec(x_26);
x_29 = l_Array_binSearchAux___main___at_Lean_evalConst___spec__1(x_22, x_25, x_24, x_28);
lean::dec(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_1);
x_32 = l_Lean_evalConst___rarg___closed__1;
x_33 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean::string_append(x_33, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_23);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_39 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1;
x_40 = x_38;
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_23);
return x_41;
}
}
}
else
{
uint8 x_42; 
lean::dec(x_1);
x_42 = !lean::is_exclusive(x_3);
if (x_42 == 0)
{
return x_3;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_3, 0);
x_44 = lean::cnstr_get(x_3, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_3);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
}
}
obj* l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__5(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
} else {
 lean::dec_ref(x_2);
 x_10 = lean::box(0);
}
x_11 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4(x_8, x_3);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = lean::box(0);
lean::cnstr_set(x_11, 0, x_14);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::inc(x_15);
x_16 = l___private_init_lean_parser_parser_7__updateTokens(x_1, x_15, x_11);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_35; 
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_19 = x_16;
} else {
 lean::dec_ref(x_16);
 x_19 = lean::box(0);
}
x_35 = lean::cnstr_get(x_15, 1);
lean::inc(x_35);
lean::dec(x_15);
switch (lean::obj_tag(x_35)) {
case 0:
{
x_20 = x_14;
goto block_34;
}
case 1:
{
x_20 = x_14;
goto block_34;
}
default: 
{
obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_19);
lean::dec(x_10);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::dec(x_35);
x_37 = l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__5(x_13, x_17, x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_14);
lean::cnstr_set(x_38, 1, x_18);
x_1 = x_37;
x_2 = x_9;
x_3 = x_38;
goto _start;
}
}
block_34:
{
uint8 x_21; 
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_17);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 2);
if (lean::is_scalar(x_10)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_10;
}
lean::cnstr_set(x_23, 0, x_13);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_17, 2, x_23);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_14);
lean::cnstr_set(x_24, 1, x_18);
x_1 = x_17;
x_2 = x_9;
x_3 = x_24;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_17, 0);
x_27 = lean::cnstr_get(x_17, 1);
x_28 = lean::cnstr_get(x_17, 2);
x_29 = lean::cnstr_get(x_17, 3);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_17);
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_30 = x_10;
}
lean::cnstr_set(x_30, 0, x_13);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_27);
lean::cnstr_set(x_31, 2, x_30);
lean::cnstr_set(x_31, 3, x_29);
if (lean::is_scalar(x_19)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_19;
}
lean::cnstr_set(x_32, 0, x_14);
lean::cnstr_set(x_32, 1, x_18);
x_1 = x_31;
x_2 = x_9;
x_3 = x_32;
goto _start;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_10);
lean::dec(x_9);
x_40 = !lean::is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_16, 0);
x_42 = lean::cnstr_get(x_16, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_16);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_11, 0);
x_45 = lean::cnstr_get(x_11, 1);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_11);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
lean::inc(x_48);
x_49 = l___private_init_lean_parser_parser_7__updateTokens(x_1, x_48, x_47);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_64; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_64 = lean::cnstr_get(x_48, 1);
lean::inc(x_64);
lean::dec(x_48);
switch (lean::obj_tag(x_64)) {
case 0:
{
x_53 = x_46;
goto block_63;
}
case 1:
{
x_53 = x_46;
goto block_63;
}
default: 
{
obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_52);
lean::dec(x_10);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
lean::dec(x_64);
x_66 = l_List_foldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__5(x_44, x_50, x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_46);
lean::cnstr_set(x_67, 1, x_51);
x_1 = x_66;
x_2 = x_9;
x_3 = x_67;
goto _start;
}
}
block_63:
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_53);
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_50, 2);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_50, 3);
lean::inc(x_57);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 lean::cnstr_release(x_50, 2);
 lean::cnstr_release(x_50, 3);
 x_58 = x_50;
} else {
 lean::dec_ref(x_50);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_10;
}
lean::cnstr_set(x_59, 0, x_44);
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
if (lean::is_scalar(x_52)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_52;
}
lean::cnstr_set(x_61, 0, x_46);
lean::cnstr_set(x_61, 1, x_51);
x_1 = x_60;
x_2 = x_9;
x_3 = x_61;
goto _start;
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_48);
lean::dec(x_44);
lean::dec(x_10);
lean::dec(x_9);
x_69 = lean::cnstr_get(x_49, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_49, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_71 = x_49;
} else {
 lean::dec_ref(x_49);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
uint8 x_73; 
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_1);
x_73 = !lean::is_exclusive(x_11);
if (x_73 == 0)
{
return x_11;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_11, 0);
x_75 = lean::cnstr_get(x_11, 1);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_11);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
obj* _init_l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1() {
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
obj* l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::cnstr_set(x_4, 0, x_8);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::io_ref_get(x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_10, 0);
lean::cnstr_set(x_10, 0, x_8);
x_13 = lean::cnstr_get(x_1, 2);
x_14 = lean::io_ref_get(x_13, x_10);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_14, 0);
lean::cnstr_set(x_14, 0, x_8);
x_17 = l_List_reverse___rarg(x_12);
x_18 = l_List_reverse___rarg(x_16);
x_19 = l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1;
x_20 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3(x_19, x_18, x_14);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
lean::cnstr_set(x_20, 0, x_8);
x_23 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(x_22, x_17, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_20);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_8);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(x_24, x_17, x_26);
return x_27;
}
}
else
{
uint8 x_28; 
lean::dec(x_17);
x_28 = !lean::is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_20, 0);
x_30 = lean::cnstr_get(x_20, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_20);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_14, 0);
x_33 = lean::cnstr_get(x_14, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_14);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_8);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_List_reverse___rarg(x_12);
x_36 = l_List_reverse___rarg(x_32);
x_37 = l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1;
x_38 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3(x_37, x_36, x_34);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_41 = x_38;
} else {
 lean::dec_ref(x_38);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_8);
lean::cnstr_set(x_42, 1, x_40);
x_43 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(x_39, x_35, x_42);
return x_43;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_35);
x_44 = lean::cnstr_get(x_38, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_46 = x_38;
} else {
 lean::dec_ref(x_38);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8 x_48; 
lean::dec(x_12);
x_48 = !lean::is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_14, 0);
x_50 = lean::cnstr_get(x_14, 1);
lean::inc(x_50);
lean::inc(x_49);
lean::dec(x_14);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_10, 0);
x_53 = lean::cnstr_get(x_10, 1);
lean::inc(x_53);
lean::inc(x_52);
lean::dec(x_10);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_8);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::cnstr_get(x_1, 2);
x_56 = lean::io_ref_get(x_55, x_54);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_59 = x_56;
} else {
 lean::dec_ref(x_56);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_8);
lean::cnstr_set(x_60, 1, x_58);
x_61 = l_List_reverse___rarg(x_52);
x_62 = l_List_reverse___rarg(x_57);
x_63 = l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1;
x_64 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3(x_63, x_62, x_60);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_67 = x_64;
} else {
 lean::dec_ref(x_64);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_8);
lean::cnstr_set(x_68, 1, x_66);
x_69 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(x_65, x_61, x_68);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_61);
x_70 = lean::cnstr_get(x_64, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_64, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_72 = x_64;
} else {
 lean::dec_ref(x_64);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_52);
x_74 = lean::cnstr_get(x_56, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_56, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_76 = x_56;
} else {
 lean::dec_ref(x_56);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
uint8 x_78; 
x_78 = !lean::is_exclusive(x_10);
if (x_78 == 0)
{
return x_10;
}
else
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::cnstr_get(x_10, 0);
x_80 = lean::cnstr_get(x_10, 1);
lean::inc(x_80);
lean::inc(x_79);
lean::dec(x_10);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_82 = lean::cnstr_get(x_4, 1);
lean::inc(x_82);
lean::dec(x_4);
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_82);
x_85 = lean::cnstr_get(x_1, 1);
x_86 = lean::io_ref_get(x_85, x_84);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_89 = x_86;
} else {
 lean::dec_ref(x_86);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_83);
lean::cnstr_set(x_90, 1, x_88);
x_91 = lean::cnstr_get(x_1, 2);
x_92 = lean::io_ref_get(x_91, x_90);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_83);
lean::cnstr_set(x_96, 1, x_94);
x_97 = l_List_reverse___rarg(x_87);
x_98 = l_List_reverse___rarg(x_93);
x_99 = l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1;
x_100 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3(x_99, x_98, x_96);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_100, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_103 = x_100;
} else {
 lean::dec_ref(x_100);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_83);
lean::cnstr_set(x_104, 1, x_102);
x_105 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__6(x_101, x_97, x_104);
return x_105;
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_97);
x_106 = lean::cnstr_get(x_100, 0);
lean::inc(x_106);
x_107 = lean::cnstr_get(x_100, 1);
lean::inc(x_107);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_108 = x_100;
} else {
 lean::dec_ref(x_100);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
lean::cnstr_set(x_109, 1, x_107);
return x_109;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_87);
x_110 = lean::cnstr_get(x_92, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_92, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_112 = x_92;
} else {
 lean::dec_ref(x_92);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
lean::cnstr_set(x_113, 1, x_111);
return x_113;
}
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_86, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_86, 1);
lean::inc(x_115);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_116 = x_86;
} else {
 lean::dec_ref(x_86);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
lean::cnstr_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
uint8 x_118; 
x_118 = !lean::is_exclusive(x_4);
if (x_118 == 0)
{
obj* x_119; obj* x_120; 
x_119 = lean::cnstr_get(x_4, 0);
lean::dec(x_119);
x_120 = lean::cnstr_get(x_5, 0);
lean::inc(x_120);
lean::dec(x_5);
lean::cnstr_set(x_4, 0, x_120);
return x_4;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_4, 1);
lean::inc(x_121);
lean::dec(x_4);
x_122 = lean::cnstr_get(x_5, 0);
lean::inc(x_122);
lean::dec(x_5);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8 x_124; 
x_124 = !lean::is_exclusive(x_4);
if (x_124 == 0)
{
return x_4;
}
else
{
obj* x_125; obj* x_126; obj* x_127; 
x_125 = lean::cnstr_get(x_4, 0);
x_126 = lean::cnstr_get(x_4, 1);
lean::inc(x_126);
lean::inc(x_125);
lean::dec(x_4);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_126);
return x_127;
}
}
}
}
obj* l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_BuiltinParserAttribute_getTables___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Parser_BuiltinParserAttribute_getTables(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_BuiltinParserAttribute_getTables___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_BuiltinParserAttribute_getTables___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_BuiltinParserAttribute_getTables(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_BuiltinParserAttribute_runParser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe(x_1, x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_Lean_Parser_runParser(x_2, x_8, x_3, x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
lean::cnstr_set_tag(x_6, 1);
lean::cnstr_set(x_6, 0, x_10);
return x_6;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
lean::cnstr_set(x_6, 0, x_11);
return x_6;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_6);
x_14 = l_Lean_Parser_runParser(x_2, x_12, x_3, x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
}
}
else
{
uint8 x_19; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_19 = !lean::is_exclusive(x_6);
if (x_19 == 0)
{
return x_6;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_6, 0);
x_21 = lean::cnstr_get(x_6, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_6);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
}
}
obj* l_Lean_Parser_BuiltinParserAttribute_runParser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_BuiltinParserAttribute_runParser(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected parser type at '");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' (`Parser` or `TrailingParser` expected");
return x_1;
}
}
obj* l___private_init_lean_parser_parser_8__throwUnexpectedParserType(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::dec(x_4);
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_1);
x_7 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2;
x_10 = lean::string_append(x_8, x_9);
lean::cnstr_set_tag(x_2, 1);
lean::cnstr_set(x_2, 0, x_10);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_16 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2;
x_17 = lean::string_append(x_15, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
}
}
obj* l___private_init_lean_parser_parser_9__updateTokens(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::io_ref_get(x_2, x_3);
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
x_8 = lean::io_ref_reset(x_2, x_4);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_8, 1);
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
lean::inc(x_10);
lean::cnstr_set(x_8, 0, x_7);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_13 = !lean::is_exclusive(x_6);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_6, 0);
x_15 = lean::cnstr_get(x_6, 1);
x_16 = lean::cnstr_get(x_6, 2);
x_17 = lean::cnstr_get(x_6, 3);
x_18 = lean::apply_1(x_12, x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
lean::free_heap_obj(x_6);
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_8);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_10);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
lean::dec(x_18);
lean::cnstr_set(x_6, 3, x_21);
x_22 = lean::io_ref_set(x_2, x_6, x_8);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_6, 0);
x_24 = lean::cnstr_get(x_6, 1);
x_25 = lean::cnstr_get(x_6, 2);
x_26 = lean::cnstr_get(x_6, 3);
lean::inc(x_26);
lean::inc(x_25);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_6);
x_27 = lean::apply_1(x_12, x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_25);
lean::dec(x_24);
lean::dec(x_23);
lean::dec(x_8);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
lean::dec(x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_10);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
x_31 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_31, 0, x_23);
lean::cnstr_set(x_31, 1, x_24);
lean::cnstr_set(x_31, 2, x_25);
lean::cnstr_set(x_31, 3, x_30);
x_32 = lean::io_ref_set(x_2, x_31, x_8);
return x_32;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_8, 1);
lean::inc(x_33);
lean::dec(x_8);
lean::inc(x_33);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_6, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_6, 1);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_6, 2);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_6, 3);
lean::inc(x_39);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 lean::cnstr_release(x_6, 3);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
x_41 = lean::apply_1(x_35, x_39);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_40);
lean::dec(x_38);
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_34);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_33);
return x_43;
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_33);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
lean::dec(x_41);
if (lean::is_scalar(x_40)) {
 x_45 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_45 = x_40;
}
lean::cnstr_set(x_45, 0, x_36);
lean::cnstr_set(x_45, 1, x_37);
lean::cnstr_set(x_45, 2, x_38);
lean::cnstr_set(x_45, 3, x_44);
x_46 = lean::io_ref_set(x_2, x_45, x_34);
return x_46;
}
}
}
else
{
uint8 x_47; 
lean::dec(x_6);
lean::dec(x_1);
x_47 = !lean::is_exclusive(x_8);
if (x_47 == 0)
{
return x_8;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_8, 0);
x_49 = lean::cnstr_get(x_8, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_8);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_4, 0);
x_52 = lean::cnstr_get(x_4, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_4);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::io_ref_reset(x_2, x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_57 = x_55;
} else {
 lean::dec_ref(x_55);
 x_57 = lean::box(0);
}
lean::inc(x_56);
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_56);
x_59 = lean::cnstr_get(x_1, 0);
lean::inc(x_59);
lean::dec(x_1);
x_60 = lean::cnstr_get(x_51, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_51, 1);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_51, 2);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_51, 3);
lean::inc(x_63);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 lean::cnstr_release(x_51, 2);
 lean::cnstr_release(x_51, 3);
 x_64 = x_51;
} else {
 lean::dec_ref(x_51);
 x_64 = lean::box(0);
}
x_65 = lean::apply_1(x_59, x_63);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_64);
lean::dec(x_62);
lean::dec(x_61);
lean::dec(x_60);
lean::dec(x_58);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
lean::dec(x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_56);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_56);
x_68 = lean::cnstr_get(x_65, 0);
lean::inc(x_68);
lean::dec(x_65);
if (lean::is_scalar(x_64)) {
 x_69 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_69 = x_64;
}
lean::cnstr_set(x_69, 0, x_60);
lean::cnstr_set(x_69, 1, x_61);
lean::cnstr_set(x_69, 2, x_62);
lean::cnstr_set(x_69, 3, x_68);
x_70 = lean::io_ref_set(x_2, x_69, x_58);
return x_70;
}
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_51);
lean::dec(x_1);
x_71 = lean::cnstr_get(x_55, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_55, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_73 = x_55;
} else {
 lean::dec_ref(x_55);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8 x_75; 
lean::dec(x_1);
x_75 = !lean::is_exclusive(x_4);
if (x_75 == 0)
{
return x_4;
}
else
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = lean::cnstr_get(x_4, 0);
x_77 = lean::cnstr_get(x_4, 1);
lean::inc(x_77);
lean::inc(x_76);
lean::dec(x_4);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
return x_78;
}
}
}
}
obj* l___private_init_lean_parser_parser_9__updateTokens___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_parser_9__updateTokens(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(obj* x_1, obj* x_2, obj* x_3) {
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
obj* _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown declaration");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2() {
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
obj* _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3() {
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
obj* _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4() {
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
x_8 = lean::mk_string("nud");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
x_8 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1;
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_10 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_13 = l_Lean_ConstantInfo_type(x_12);
lean::dec(x_12);
switch (lean::obj_tag(x_13)) {
case 4:
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_15 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2;
x_16 = lean_name_dec_eq(x_14, x_15);
lean::dec(x_14);
if (x_16 == 0)
{
obj* x_17; 
x_17 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_2, x_4);
return x_17;
}
else
{
obj* x_18; 
x_18 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4(x_2, x_4);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = lean::box(0);
lean::cnstr_set(x_18, 0, x_21);
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::inc(x_22);
x_23 = l___private_init_lean_parser_parser_9__updateTokens(x_22, x_3, x_18);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::dec(x_25);
lean::cnstr_set(x_23, 0, x_21);
x_26 = lean::cnstr_get(x_22, 1);
lean::inc(x_26);
lean::dec(x_22);
switch (lean::obj_tag(x_26)) {
case 0:
{
obj* x_27; 
x_27 = lean::io_ref_get(x_3, x_23);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_27, 0);
lean::cnstr_set(x_27, 0, x_21);
x_30 = lean::io_ref_reset(x_3, x_27);
if (lean::obj_tag(x_30) == 0)
{
uint8 x_31; 
x_31 = !lean::is_exclusive(x_30);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_30, 0);
lean::dec(x_32);
lean::cnstr_set(x_30, 0, x_21);
x_33 = !lean::is_exclusive(x_29);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_29, 2);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_20);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set(x_29, 2, x_35);
x_36 = lean::io_ref_set(x_3, x_29, x_30);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_37 = lean::cnstr_get(x_29, 0);
x_38 = lean::cnstr_get(x_29, 1);
x_39 = lean::cnstr_get(x_29, 2);
x_40 = lean::cnstr_get(x_29, 3);
lean::inc(x_40);
lean::inc(x_39);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_29);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_20);
lean::cnstr_set(x_41, 1, x_39);
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_38);
lean::cnstr_set(x_42, 2, x_41);
lean::cnstr_set(x_42, 3, x_40);
x_43 = lean::io_ref_set(x_3, x_42, x_30);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_44 = lean::cnstr_get(x_30, 1);
lean::inc(x_44);
lean::dec(x_30);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_21);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::cnstr_get(x_29, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_29, 1);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_29, 2);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_29, 3);
lean::inc(x_49);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 lean::cnstr_release(x_29, 1);
 lean::cnstr_release(x_29, 2);
 lean::cnstr_release(x_29, 3);
 x_50 = x_29;
} else {
 lean::dec_ref(x_29);
 x_50 = lean::box(0);
}
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_20);
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
x_53 = lean::io_ref_set(x_3, x_52, x_45);
return x_53;
}
}
else
{
uint8 x_54; 
lean::dec(x_29);
lean::dec(x_20);
x_54 = !lean::is_exclusive(x_30);
if (x_54 == 0)
{
return x_30;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_30, 0);
x_56 = lean::cnstr_get(x_30, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_30);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_27, 0);
x_59 = lean::cnstr_get(x_27, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_27);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_21);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::io_ref_reset(x_3, x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_63 = x_61;
} else {
 lean::dec_ref(x_61);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_21);
lean::cnstr_set(x_64, 1, x_62);
x_65 = lean::cnstr_get(x_58, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_58, 1);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_58, 2);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_58, 3);
lean::inc(x_68);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 lean::cnstr_release(x_58, 2);
 lean::cnstr_release(x_58, 3);
 x_69 = x_58;
} else {
 lean::dec_ref(x_58);
 x_69 = lean::box(0);
}
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_20);
lean::cnstr_set(x_70, 1, x_67);
if (lean::is_scalar(x_69)) {
 x_71 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_71 = x_69;
}
lean::cnstr_set(x_71, 0, x_65);
lean::cnstr_set(x_71, 1, x_66);
lean::cnstr_set(x_71, 2, x_70);
lean::cnstr_set(x_71, 3, x_68);
x_72 = lean::io_ref_set(x_3, x_71, x_64);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_58);
lean::dec(x_20);
x_73 = lean::cnstr_get(x_61, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_61, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_75 = x_61;
} else {
 lean::dec_ref(x_61);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8 x_77; 
lean::dec(x_20);
x_77 = !lean::is_exclusive(x_27);
if (x_77 == 0)
{
return x_27;
}
else
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::cnstr_get(x_27, 0);
x_79 = lean::cnstr_get(x_27, 1);
lean::inc(x_79);
lean::inc(x_78);
lean::dec(x_27);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
return x_80;
}
}
}
case 1:
{
obj* x_81; 
x_81 = lean::io_ref_get(x_3, x_23);
if (lean::obj_tag(x_81) == 0)
{
uint8 x_82; 
x_82 = !lean::is_exclusive(x_81);
if (x_82 == 0)
{
obj* x_83; obj* x_84; 
x_83 = lean::cnstr_get(x_81, 0);
lean::cnstr_set(x_81, 0, x_21);
x_84 = lean::io_ref_reset(x_3, x_81);
if (lean::obj_tag(x_84) == 0)
{
uint8 x_85; 
x_85 = !lean::is_exclusive(x_84);
if (x_85 == 0)
{
obj* x_86; uint8 x_87; 
x_86 = lean::cnstr_get(x_84, 0);
lean::dec(x_86);
lean::cnstr_set(x_84, 0, x_21);
x_87 = !lean::is_exclusive(x_83);
if (x_87 == 0)
{
obj* x_88; obj* x_89; obj* x_90; 
x_88 = lean::cnstr_get(x_83, 2);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_20);
lean::cnstr_set(x_89, 1, x_88);
lean::cnstr_set(x_83, 2, x_89);
x_90 = lean::io_ref_set(x_3, x_83, x_84);
return x_90;
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_83, 0);
x_92 = lean::cnstr_get(x_83, 1);
x_93 = lean::cnstr_get(x_83, 2);
x_94 = lean::cnstr_get(x_83, 3);
lean::inc(x_94);
lean::inc(x_93);
lean::inc(x_92);
lean::inc(x_91);
lean::dec(x_83);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_20);
lean::cnstr_set(x_95, 1, x_93);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_91);
lean::cnstr_set(x_96, 1, x_92);
lean::cnstr_set(x_96, 2, x_95);
lean::cnstr_set(x_96, 3, x_94);
x_97 = lean::io_ref_set(x_3, x_96, x_84);
return x_97;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_98 = lean::cnstr_get(x_84, 1);
lean::inc(x_98);
lean::dec(x_84);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_21);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::cnstr_get(x_83, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_83, 1);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_83, 2);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_83, 3);
lean::inc(x_103);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 lean::cnstr_release(x_83, 2);
 lean::cnstr_release(x_83, 3);
 x_104 = x_83;
} else {
 lean::dec_ref(x_83);
 x_104 = lean::box(0);
}
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_20);
lean::cnstr_set(x_105, 1, x_102);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_100);
lean::cnstr_set(x_106, 1, x_101);
lean::cnstr_set(x_106, 2, x_105);
lean::cnstr_set(x_106, 3, x_103);
x_107 = lean::io_ref_set(x_3, x_106, x_99);
return x_107;
}
}
else
{
uint8 x_108; 
lean::dec(x_83);
lean::dec(x_20);
x_108 = !lean::is_exclusive(x_84);
if (x_108 == 0)
{
return x_84;
}
else
{
obj* x_109; obj* x_110; obj* x_111; 
x_109 = lean::cnstr_get(x_84, 0);
x_110 = lean::cnstr_get(x_84, 1);
lean::inc(x_110);
lean::inc(x_109);
lean::dec(x_84);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_109);
lean::cnstr_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_112 = lean::cnstr_get(x_81, 0);
x_113 = lean::cnstr_get(x_81, 1);
lean::inc(x_113);
lean::inc(x_112);
lean::dec(x_81);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_21);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::io_ref_reset(x_3, x_114);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_116 = lean::cnstr_get(x_115, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_117 = x_115;
} else {
 lean::dec_ref(x_115);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_21);
lean::cnstr_set(x_118, 1, x_116);
x_119 = lean::cnstr_get(x_112, 0);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_112, 1);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_112, 2);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_112, 3);
lean::inc(x_122);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 lean::cnstr_release(x_112, 2);
 lean::cnstr_release(x_112, 3);
 x_123 = x_112;
} else {
 lean::dec_ref(x_112);
 x_123 = lean::box(0);
}
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_20);
lean::cnstr_set(x_124, 1, x_121);
if (lean::is_scalar(x_123)) {
 x_125 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_125 = x_123;
}
lean::cnstr_set(x_125, 0, x_119);
lean::cnstr_set(x_125, 1, x_120);
lean::cnstr_set(x_125, 2, x_124);
lean::cnstr_set(x_125, 3, x_122);
x_126 = lean::io_ref_set(x_3, x_125, x_118);
return x_126;
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_112);
lean::dec(x_20);
x_127 = lean::cnstr_get(x_115, 0);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_115, 1);
lean::inc(x_128);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_129 = x_115;
} else {
 lean::dec_ref(x_115);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
lean::cnstr_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
uint8 x_131; 
lean::dec(x_20);
x_131 = !lean::is_exclusive(x_81);
if (x_131 == 0)
{
return x_81;
}
else
{
obj* x_132; obj* x_133; obj* x_134; 
x_132 = lean::cnstr_get(x_81, 0);
x_133 = lean::cnstr_get(x_81, 1);
lean::inc(x_133);
lean::inc(x_132);
lean::dec(x_81);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_132);
lean::cnstr_set(x_134, 1, x_133);
return x_134;
}
}
}
default: 
{
obj* x_135; obj* x_136; 
x_135 = lean::cnstr_get(x_26, 0);
lean::inc(x_135);
lean::dec(x_26);
x_136 = lean::io_ref_get(x_3, x_23);
if (lean::obj_tag(x_136) == 0)
{
uint8 x_137; 
x_137 = !lean::is_exclusive(x_136);
if (x_137 == 0)
{
obj* x_138; obj* x_139; 
x_138 = lean::cnstr_get(x_136, 0);
lean::cnstr_set(x_136, 0, x_21);
x_139 = lean::io_ref_reset(x_3, x_136);
if (lean::obj_tag(x_139) == 0)
{
uint8 x_140; 
x_140 = !lean::is_exclusive(x_139);
if (x_140 == 0)
{
obj* x_141; obj* x_142; obj* x_143; 
x_141 = lean::cnstr_get(x_139, 0);
lean::dec(x_141);
lean::cnstr_set(x_139, 0, x_21);
x_142 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(x_20, x_138, x_135);
x_143 = lean::io_ref_set(x_3, x_142, x_139);
return x_143;
}
else
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_144 = lean::cnstr_get(x_139, 1);
lean::inc(x_144);
lean::dec(x_139);
x_145 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_145, 0, x_21);
lean::cnstr_set(x_145, 1, x_144);
x_146 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(x_20, x_138, x_135);
x_147 = lean::io_ref_set(x_3, x_146, x_145);
return x_147;
}
}
else
{
uint8 x_148; 
lean::dec(x_138);
lean::dec(x_135);
lean::dec(x_20);
x_148 = !lean::is_exclusive(x_139);
if (x_148 == 0)
{
return x_139;
}
else
{
obj* x_149; obj* x_150; obj* x_151; 
x_149 = lean::cnstr_get(x_139, 0);
x_150 = lean::cnstr_get(x_139, 1);
lean::inc(x_150);
lean::inc(x_149);
lean::dec(x_139);
x_151 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_151, 0, x_149);
lean::cnstr_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_152 = lean::cnstr_get(x_136, 0);
x_153 = lean::cnstr_get(x_136, 1);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_136);
x_154 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_154, 0, x_21);
lean::cnstr_set(x_154, 1, x_153);
x_155 = lean::io_ref_reset(x_3, x_154);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_156 = lean::cnstr_get(x_155, 1);
lean::inc(x_156);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_157 = x_155;
} else {
 lean::dec_ref(x_155);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_21);
lean::cnstr_set(x_158, 1, x_156);
x_159 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(x_20, x_152, x_135);
x_160 = lean::io_ref_set(x_3, x_159, x_158);
return x_160;
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_152);
lean::dec(x_135);
lean::dec(x_20);
x_161 = lean::cnstr_get(x_155, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_155, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_163 = x_155;
} else {
 lean::dec_ref(x_155);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
lean::cnstr_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
uint8 x_165; 
lean::dec(x_135);
lean::dec(x_20);
x_165 = !lean::is_exclusive(x_136);
if (x_165 == 0)
{
return x_136;
}
else
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_136, 0);
x_167 = lean::cnstr_get(x_136, 1);
lean::inc(x_167);
lean::inc(x_166);
lean::dec(x_136);
x_168 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
else
{
obj* x_169; obj* x_170; obj* x_171; 
x_169 = lean::cnstr_get(x_23, 1);
lean::inc(x_169);
lean::dec(x_23);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_21);
lean::cnstr_set(x_170, 1, x_169);
x_171 = lean::cnstr_get(x_22, 1);
lean::inc(x_171);
lean::dec(x_22);
switch (lean::obj_tag(x_171)) {
case 0:
{
obj* x_172; 
x_172 = lean::io_ref_get(x_3, x_170);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_172, 1);
lean::inc(x_174);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 x_175 = x_172;
} else {
 lean::dec_ref(x_172);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_21);
lean::cnstr_set(x_176, 1, x_174);
x_177 = lean::io_ref_reset(x_3, x_176);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_178 = lean::cnstr_get(x_177, 1);
lean::inc(x_178);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_179 = x_177;
} else {
 lean::dec_ref(x_177);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_21);
lean::cnstr_set(x_180, 1, x_178);
x_181 = lean::cnstr_get(x_173, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_173, 1);
lean::inc(x_182);
x_183 = lean::cnstr_get(x_173, 2);
lean::inc(x_183);
x_184 = lean::cnstr_get(x_173, 3);
lean::inc(x_184);
if (lean::is_exclusive(x_173)) {
 lean::cnstr_release(x_173, 0);
 lean::cnstr_release(x_173, 1);
 lean::cnstr_release(x_173, 2);
 lean::cnstr_release(x_173, 3);
 x_185 = x_173;
} else {
 lean::dec_ref(x_173);
 x_185 = lean::box(0);
}
x_186 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_186, 0, x_20);
lean::cnstr_set(x_186, 1, x_183);
if (lean::is_scalar(x_185)) {
 x_187 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_187 = x_185;
}
lean::cnstr_set(x_187, 0, x_181);
lean::cnstr_set(x_187, 1, x_182);
lean::cnstr_set(x_187, 2, x_186);
lean::cnstr_set(x_187, 3, x_184);
x_188 = lean::io_ref_set(x_3, x_187, x_180);
return x_188;
}
else
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
lean::dec(x_173);
lean::dec(x_20);
x_189 = lean::cnstr_get(x_177, 0);
lean::inc(x_189);
x_190 = lean::cnstr_get(x_177, 1);
lean::inc(x_190);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_191 = x_177;
} else {
 lean::dec_ref(x_177);
 x_191 = lean::box(0);
}
if (lean::is_scalar(x_191)) {
 x_192 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_192 = x_191;
}
lean::cnstr_set(x_192, 0, x_189);
lean::cnstr_set(x_192, 1, x_190);
return x_192;
}
}
else
{
obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_20);
x_193 = lean::cnstr_get(x_172, 0);
lean::inc(x_193);
x_194 = lean::cnstr_get(x_172, 1);
lean::inc(x_194);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 x_195 = x_172;
} else {
 lean::dec_ref(x_172);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
lean::cnstr_set(x_196, 1, x_194);
return x_196;
}
}
case 1:
{
obj* x_197; 
x_197 = lean::io_ref_get(x_3, x_170);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
x_198 = lean::cnstr_get(x_197, 0);
lean::inc(x_198);
x_199 = lean::cnstr_get(x_197, 1);
lean::inc(x_199);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 x_200 = x_197;
} else {
 lean::dec_ref(x_197);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_21);
lean::cnstr_set(x_201, 1, x_199);
x_202 = lean::io_ref_reset(x_3, x_201);
if (lean::obj_tag(x_202) == 0)
{
obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
x_203 = lean::cnstr_get(x_202, 1);
lean::inc(x_203);
if (lean::is_exclusive(x_202)) {
 lean::cnstr_release(x_202, 0);
 lean::cnstr_release(x_202, 1);
 x_204 = x_202;
} else {
 lean::dec_ref(x_202);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_21);
lean::cnstr_set(x_205, 1, x_203);
x_206 = lean::cnstr_get(x_198, 0);
lean::inc(x_206);
x_207 = lean::cnstr_get(x_198, 1);
lean::inc(x_207);
x_208 = lean::cnstr_get(x_198, 2);
lean::inc(x_208);
x_209 = lean::cnstr_get(x_198, 3);
lean::inc(x_209);
if (lean::is_exclusive(x_198)) {
 lean::cnstr_release(x_198, 0);
 lean::cnstr_release(x_198, 1);
 lean::cnstr_release(x_198, 2);
 lean::cnstr_release(x_198, 3);
 x_210 = x_198;
} else {
 lean::dec_ref(x_198);
 x_210 = lean::box(0);
}
x_211 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_211, 0, x_20);
lean::cnstr_set(x_211, 1, x_208);
if (lean::is_scalar(x_210)) {
 x_212 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_212 = x_210;
}
lean::cnstr_set(x_212, 0, x_206);
lean::cnstr_set(x_212, 1, x_207);
lean::cnstr_set(x_212, 2, x_211);
lean::cnstr_set(x_212, 3, x_209);
x_213 = lean::io_ref_set(x_3, x_212, x_205);
return x_213;
}
else
{
obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_198);
lean::dec(x_20);
x_214 = lean::cnstr_get(x_202, 0);
lean::inc(x_214);
x_215 = lean::cnstr_get(x_202, 1);
lean::inc(x_215);
if (lean::is_exclusive(x_202)) {
 lean::cnstr_release(x_202, 0);
 lean::cnstr_release(x_202, 1);
 x_216 = x_202;
} else {
 lean::dec_ref(x_202);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
lean::cnstr_set(x_217, 1, x_215);
return x_217;
}
}
else
{
obj* x_218; obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_20);
x_218 = lean::cnstr_get(x_197, 0);
lean::inc(x_218);
x_219 = lean::cnstr_get(x_197, 1);
lean::inc(x_219);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 x_220 = x_197;
} else {
 lean::dec_ref(x_197);
 x_220 = lean::box(0);
}
if (lean::is_scalar(x_220)) {
 x_221 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_221 = x_220;
}
lean::cnstr_set(x_221, 0, x_218);
lean::cnstr_set(x_221, 1, x_219);
return x_221;
}
}
default: 
{
obj* x_222; obj* x_223; 
x_222 = lean::cnstr_get(x_171, 0);
lean::inc(x_222);
lean::dec(x_171);
x_223 = lean::io_ref_get(x_3, x_170);
if (lean::obj_tag(x_223) == 0)
{
obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_225 = lean::cnstr_get(x_223, 1);
lean::inc(x_225);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_226 = x_223;
} else {
 lean::dec_ref(x_223);
 x_226 = lean::box(0);
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_21);
lean::cnstr_set(x_227, 1, x_225);
x_228 = lean::io_ref_reset(x_3, x_227);
if (lean::obj_tag(x_228) == 0)
{
obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_229 = lean::cnstr_get(x_228, 1);
lean::inc(x_229);
if (lean::is_exclusive(x_228)) {
 lean::cnstr_release(x_228, 0);
 lean::cnstr_release(x_228, 1);
 x_230 = x_228;
} else {
 lean::dec_ref(x_228);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_21);
lean::cnstr_set(x_231, 1, x_229);
x_232 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(x_20, x_224, x_222);
x_233 = lean::io_ref_set(x_3, x_232, x_231);
return x_233;
}
else
{
obj* x_234; obj* x_235; obj* x_236; obj* x_237; 
lean::dec(x_224);
lean::dec(x_222);
lean::dec(x_20);
x_234 = lean::cnstr_get(x_228, 0);
lean::inc(x_234);
x_235 = lean::cnstr_get(x_228, 1);
lean::inc(x_235);
if (lean::is_exclusive(x_228)) {
 lean::cnstr_release(x_228, 0);
 lean::cnstr_release(x_228, 1);
 x_236 = x_228;
} else {
 lean::dec_ref(x_228);
 x_236 = lean::box(0);
}
if (lean::is_scalar(x_236)) {
 x_237 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_237 = x_236;
}
lean::cnstr_set(x_237, 0, x_234);
lean::cnstr_set(x_237, 1, x_235);
return x_237;
}
}
else
{
obj* x_238; obj* x_239; obj* x_240; obj* x_241; 
lean::dec(x_222);
lean::dec(x_20);
x_238 = lean::cnstr_get(x_223, 0);
lean::inc(x_238);
x_239 = lean::cnstr_get(x_223, 1);
lean::inc(x_239);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_240 = x_223;
} else {
 lean::dec_ref(x_223);
 x_240 = lean::box(0);
}
if (lean::is_scalar(x_240)) {
 x_241 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_241 = x_240;
}
lean::cnstr_set(x_241, 0, x_238);
lean::cnstr_set(x_241, 1, x_239);
return x_241;
}
}
}
}
}
else
{
uint8 x_242; 
lean::dec(x_22);
lean::dec(x_20);
x_242 = !lean::is_exclusive(x_23);
if (x_242 == 0)
{
return x_23;
}
else
{
obj* x_243; obj* x_244; obj* x_245; 
x_243 = lean::cnstr_get(x_23, 0);
x_244 = lean::cnstr_get(x_23, 1);
lean::inc(x_244);
lean::inc(x_243);
lean::dec(x_23);
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_243);
lean::cnstr_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
x_246 = lean::cnstr_get(x_18, 0);
x_247 = lean::cnstr_get(x_18, 1);
lean::inc(x_247);
lean::inc(x_246);
lean::dec(x_18);
x_248 = lean::box(0);
x_249 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_247);
x_250 = lean::cnstr_get(x_246, 0);
lean::inc(x_250);
lean::inc(x_250);
x_251 = l___private_init_lean_parser_parser_9__updateTokens(x_250, x_3, x_249);
if (lean::obj_tag(x_251) == 0)
{
obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
x_252 = lean::cnstr_get(x_251, 1);
lean::inc(x_252);
if (lean::is_exclusive(x_251)) {
 lean::cnstr_release(x_251, 0);
 lean::cnstr_release(x_251, 1);
 x_253 = x_251;
} else {
 lean::dec_ref(x_251);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_248);
lean::cnstr_set(x_254, 1, x_252);
x_255 = lean::cnstr_get(x_250, 1);
lean::inc(x_255);
lean::dec(x_250);
switch (lean::obj_tag(x_255)) {
case 0:
{
obj* x_256; 
x_256 = lean::io_ref_get(x_3, x_254);
if (lean::obj_tag(x_256) == 0)
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_257 = lean::cnstr_get(x_256, 0);
lean::inc(x_257);
x_258 = lean::cnstr_get(x_256, 1);
lean::inc(x_258);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 lean::cnstr_release(x_256, 1);
 x_259 = x_256;
} else {
 lean::dec_ref(x_256);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_248);
lean::cnstr_set(x_260, 1, x_258);
x_261 = lean::io_ref_reset(x_3, x_260);
if (lean::obj_tag(x_261) == 0)
{
obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_262 = lean::cnstr_get(x_261, 1);
lean::inc(x_262);
if (lean::is_exclusive(x_261)) {
 lean::cnstr_release(x_261, 0);
 lean::cnstr_release(x_261, 1);
 x_263 = x_261;
} else {
 lean::dec_ref(x_261);
 x_263 = lean::box(0);
}
if (lean::is_scalar(x_263)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_263;
}
lean::cnstr_set(x_264, 0, x_248);
lean::cnstr_set(x_264, 1, x_262);
x_265 = lean::cnstr_get(x_257, 0);
lean::inc(x_265);
x_266 = lean::cnstr_get(x_257, 1);
lean::inc(x_266);
x_267 = lean::cnstr_get(x_257, 2);
lean::inc(x_267);
x_268 = lean::cnstr_get(x_257, 3);
lean::inc(x_268);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 lean::cnstr_release(x_257, 2);
 lean::cnstr_release(x_257, 3);
 x_269 = x_257;
} else {
 lean::dec_ref(x_257);
 x_269 = lean::box(0);
}
x_270 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_270, 0, x_246);
lean::cnstr_set(x_270, 1, x_267);
if (lean::is_scalar(x_269)) {
 x_271 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_271 = x_269;
}
lean::cnstr_set(x_271, 0, x_265);
lean::cnstr_set(x_271, 1, x_266);
lean::cnstr_set(x_271, 2, x_270);
lean::cnstr_set(x_271, 3, x_268);
x_272 = lean::io_ref_set(x_3, x_271, x_264);
return x_272;
}
else
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_257);
lean::dec(x_246);
x_273 = lean::cnstr_get(x_261, 0);
lean::inc(x_273);
x_274 = lean::cnstr_get(x_261, 1);
lean::inc(x_274);
if (lean::is_exclusive(x_261)) {
 lean::cnstr_release(x_261, 0);
 lean::cnstr_release(x_261, 1);
 x_275 = x_261;
} else {
 lean::dec_ref(x_261);
 x_275 = lean::box(0);
}
if (lean::is_scalar(x_275)) {
 x_276 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_276 = x_275;
}
lean::cnstr_set(x_276, 0, x_273);
lean::cnstr_set(x_276, 1, x_274);
return x_276;
}
}
else
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
lean::dec(x_246);
x_277 = lean::cnstr_get(x_256, 0);
lean::inc(x_277);
x_278 = lean::cnstr_get(x_256, 1);
lean::inc(x_278);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 lean::cnstr_release(x_256, 1);
 x_279 = x_256;
} else {
 lean::dec_ref(x_256);
 x_279 = lean::box(0);
}
if (lean::is_scalar(x_279)) {
 x_280 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_280 = x_279;
}
lean::cnstr_set(x_280, 0, x_277);
lean::cnstr_set(x_280, 1, x_278);
return x_280;
}
}
case 1:
{
obj* x_281; 
x_281 = lean::io_ref_get(x_3, x_254);
if (lean::obj_tag(x_281) == 0)
{
obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; 
x_282 = lean::cnstr_get(x_281, 0);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_281, 1);
lean::inc(x_283);
if (lean::is_exclusive(x_281)) {
 lean::cnstr_release(x_281, 0);
 lean::cnstr_release(x_281, 1);
 x_284 = x_281;
} else {
 lean::dec_ref(x_281);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_248);
lean::cnstr_set(x_285, 1, x_283);
x_286 = lean::io_ref_reset(x_3, x_285);
if (lean::obj_tag(x_286) == 0)
{
obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
x_287 = lean::cnstr_get(x_286, 1);
lean::inc(x_287);
if (lean::is_exclusive(x_286)) {
 lean::cnstr_release(x_286, 0);
 lean::cnstr_release(x_286, 1);
 x_288 = x_286;
} else {
 lean::dec_ref(x_286);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_248);
lean::cnstr_set(x_289, 1, x_287);
x_290 = lean::cnstr_get(x_282, 0);
lean::inc(x_290);
x_291 = lean::cnstr_get(x_282, 1);
lean::inc(x_291);
x_292 = lean::cnstr_get(x_282, 2);
lean::inc(x_292);
x_293 = lean::cnstr_get(x_282, 3);
lean::inc(x_293);
if (lean::is_exclusive(x_282)) {
 lean::cnstr_release(x_282, 0);
 lean::cnstr_release(x_282, 1);
 lean::cnstr_release(x_282, 2);
 lean::cnstr_release(x_282, 3);
 x_294 = x_282;
} else {
 lean::dec_ref(x_282);
 x_294 = lean::box(0);
}
x_295 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_295, 0, x_246);
lean::cnstr_set(x_295, 1, x_292);
if (lean::is_scalar(x_294)) {
 x_296 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_296 = x_294;
}
lean::cnstr_set(x_296, 0, x_290);
lean::cnstr_set(x_296, 1, x_291);
lean::cnstr_set(x_296, 2, x_295);
lean::cnstr_set(x_296, 3, x_293);
x_297 = lean::io_ref_set(x_3, x_296, x_289);
return x_297;
}
else
{
obj* x_298; obj* x_299; obj* x_300; obj* x_301; 
lean::dec(x_282);
lean::dec(x_246);
x_298 = lean::cnstr_get(x_286, 0);
lean::inc(x_298);
x_299 = lean::cnstr_get(x_286, 1);
lean::inc(x_299);
if (lean::is_exclusive(x_286)) {
 lean::cnstr_release(x_286, 0);
 lean::cnstr_release(x_286, 1);
 x_300 = x_286;
} else {
 lean::dec_ref(x_286);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
lean::cnstr_set(x_301, 1, x_299);
return x_301;
}
}
else
{
obj* x_302; obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_246);
x_302 = lean::cnstr_get(x_281, 0);
lean::inc(x_302);
x_303 = lean::cnstr_get(x_281, 1);
lean::inc(x_303);
if (lean::is_exclusive(x_281)) {
 lean::cnstr_release(x_281, 0);
 lean::cnstr_release(x_281, 1);
 x_304 = x_281;
} else {
 lean::dec_ref(x_281);
 x_304 = lean::box(0);
}
if (lean::is_scalar(x_304)) {
 x_305 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_305 = x_304;
}
lean::cnstr_set(x_305, 0, x_302);
lean::cnstr_set(x_305, 1, x_303);
return x_305;
}
}
default: 
{
obj* x_306; obj* x_307; 
x_306 = lean::cnstr_get(x_255, 0);
lean::inc(x_306);
lean::dec(x_255);
x_307 = lean::io_ref_get(x_3, x_254);
if (lean::obj_tag(x_307) == 0)
{
obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_308 = lean::cnstr_get(x_307, 0);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_307, 1);
lean::inc(x_309);
if (lean::is_exclusive(x_307)) {
 lean::cnstr_release(x_307, 0);
 lean::cnstr_release(x_307, 1);
 x_310 = x_307;
} else {
 lean::dec_ref(x_307);
 x_310 = lean::box(0);
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_248);
lean::cnstr_set(x_311, 1, x_309);
x_312 = lean::io_ref_reset(x_3, x_311);
if (lean::obj_tag(x_312) == 0)
{
obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_313 = lean::cnstr_get(x_312, 1);
lean::inc(x_313);
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 x_314 = x_312;
} else {
 lean::dec_ref(x_312);
 x_314 = lean::box(0);
}
if (lean::is_scalar(x_314)) {
 x_315 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_315 = x_314;
}
lean::cnstr_set(x_315, 0, x_248);
lean::cnstr_set(x_315, 1, x_313);
x_316 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__1(x_246, x_308, x_306);
x_317 = lean::io_ref_set(x_3, x_316, x_315);
return x_317;
}
else
{
obj* x_318; obj* x_319; obj* x_320; obj* x_321; 
lean::dec(x_308);
lean::dec(x_306);
lean::dec(x_246);
x_318 = lean::cnstr_get(x_312, 0);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_312, 1);
lean::inc(x_319);
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 x_320 = x_312;
} else {
 lean::dec_ref(x_312);
 x_320 = lean::box(0);
}
if (lean::is_scalar(x_320)) {
 x_321 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_321 = x_320;
}
lean::cnstr_set(x_321, 0, x_318);
lean::cnstr_set(x_321, 1, x_319);
return x_321;
}
}
else
{
obj* x_322; obj* x_323; obj* x_324; obj* x_325; 
lean::dec(x_306);
lean::dec(x_246);
x_322 = lean::cnstr_get(x_307, 0);
lean::inc(x_322);
x_323 = lean::cnstr_get(x_307, 1);
lean::inc(x_323);
if (lean::is_exclusive(x_307)) {
 lean::cnstr_release(x_307, 0);
 lean::cnstr_release(x_307, 1);
 x_324 = x_307;
} else {
 lean::dec_ref(x_307);
 x_324 = lean::box(0);
}
if (lean::is_scalar(x_324)) {
 x_325 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_325 = x_324;
}
lean::cnstr_set(x_325, 0, x_322);
lean::cnstr_set(x_325, 1, x_323);
return x_325;
}
}
}
}
else
{
obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
lean::dec(x_250);
lean::dec(x_246);
x_326 = lean::cnstr_get(x_251, 0);
lean::inc(x_326);
x_327 = lean::cnstr_get(x_251, 1);
lean::inc(x_327);
if (lean::is_exclusive(x_251)) {
 lean::cnstr_release(x_251, 0);
 lean::cnstr_release(x_251, 1);
 x_328 = x_251;
} else {
 lean::dec_ref(x_251);
 x_328 = lean::box(0);
}
if (lean::is_scalar(x_328)) {
 x_329 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_329 = x_328;
}
lean::cnstr_set(x_329, 0, x_326);
lean::cnstr_set(x_329, 1, x_327);
return x_329;
}
}
}
else
{
uint8 x_330; 
x_330 = !lean::is_exclusive(x_18);
if (x_330 == 0)
{
return x_18;
}
else
{
obj* x_331; obj* x_332; obj* x_333; 
x_331 = lean::cnstr_get(x_18, 0);
x_332 = lean::cnstr_get(x_18, 1);
lean::inc(x_332);
lean::inc(x_331);
lean::dec(x_18);
x_333 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_333, 0, x_331);
lean::cnstr_set(x_333, 1, x_332);
return x_333;
}
}
}
}
case 5:
{
obj* x_334; 
x_334 = lean::cnstr_get(x_13, 0);
lean::inc(x_334);
if (lean::obj_tag(x_334) == 4)
{
obj* x_335; obj* x_336; obj* x_337; uint8 x_338; 
x_335 = lean::cnstr_get(x_13, 1);
lean::inc(x_335);
lean::dec(x_13);
x_336 = lean::cnstr_get(x_334, 0);
lean::inc(x_336);
lean::dec(x_334);
x_337 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3;
x_338 = lean_name_dec_eq(x_336, x_337);
lean::dec(x_336);
if (x_338 == 0)
{
obj* x_339; 
lean::dec(x_335);
x_339 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_2, x_4);
return x_339;
}
else
{
if (lean::obj_tag(x_335) == 4)
{
obj* x_340; obj* x_341; uint8 x_342; 
x_340 = lean::cnstr_get(x_335, 0);
lean::inc(x_340);
lean::dec(x_335);
x_341 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4;
x_342 = lean_name_dec_eq(x_340, x_341);
lean::dec(x_340);
if (x_342 == 0)
{
obj* x_343; 
x_343 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_2, x_4);
return x_343;
}
else
{
obj* x_344; 
lean::inc(x_2);
x_344 = l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1(x_2, x_4);
if (lean::obj_tag(x_344) == 0)
{
uint8 x_345; 
x_345 = !lean::is_exclusive(x_344);
if (x_345 == 0)
{
obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
x_346 = lean::cnstr_get(x_344, 0);
x_347 = lean::box(0);
lean::cnstr_set(x_344, 0, x_347);
x_348 = lean::cnstr_get(x_346, 0);
lean::inc(x_348);
lean::inc(x_348);
x_349 = l___private_init_lean_parser_parser_9__updateTokens(x_348, x_3, x_344);
if (lean::obj_tag(x_349) == 0)
{
obj* x_350; 
x_350 = lean::cnstr_get(x_348, 1);
lean::inc(x_350);
lean::dec(x_348);
switch (lean::obj_tag(x_350)) {
case 0:
{
uint8 x_351; 
lean::dec(x_346);
x_351 = !lean::is_exclusive(x_349);
if (x_351 == 0)
{
obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; 
x_352 = lean::cnstr_get(x_349, 0);
lean::dec(x_352);
x_353 = l_Lean_Name_toString___closed__1;
x_354 = l_Lean_Name_toStringWithSep___main(x_353, x_2);
x_355 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_356 = lean::string_append(x_355, x_354);
lean::dec(x_354);
x_357 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_358 = lean::string_append(x_356, x_357);
lean::cnstr_set_tag(x_349, 1);
lean::cnstr_set(x_349, 0, x_358);
return x_349;
}
else
{
obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; 
x_359 = lean::cnstr_get(x_349, 1);
lean::inc(x_359);
lean::dec(x_349);
x_360 = l_Lean_Name_toString___closed__1;
x_361 = l_Lean_Name_toStringWithSep___main(x_360, x_2);
x_362 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_363 = lean::string_append(x_362, x_361);
lean::dec(x_361);
x_364 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_365 = lean::string_append(x_363, x_364);
x_366 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_366, 0, x_365);
lean::cnstr_set(x_366, 1, x_359);
return x_366;
}
}
case 1:
{
uint8 x_367; 
lean::dec(x_346);
x_367 = !lean::is_exclusive(x_349);
if (x_367 == 0)
{
obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; 
x_368 = lean::cnstr_get(x_349, 0);
lean::dec(x_368);
x_369 = l_Lean_Name_toString___closed__1;
x_370 = l_Lean_Name_toStringWithSep___main(x_369, x_2);
x_371 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_372 = lean::string_append(x_371, x_370);
lean::dec(x_370);
x_373 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_374 = lean::string_append(x_372, x_373);
lean::cnstr_set_tag(x_349, 1);
lean::cnstr_set(x_349, 0, x_374);
return x_349;
}
else
{
obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; 
x_375 = lean::cnstr_get(x_349, 1);
lean::inc(x_375);
lean::dec(x_349);
x_376 = l_Lean_Name_toString___closed__1;
x_377 = l_Lean_Name_toStringWithSep___main(x_376, x_2);
x_378 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_379 = lean::string_append(x_378, x_377);
lean::dec(x_377);
x_380 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_381 = lean::string_append(x_379, x_380);
x_382 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_382, 0, x_381);
lean::cnstr_set(x_382, 1, x_375);
return x_382;
}
}
default: 
{
uint8 x_383; 
lean::dec(x_2);
x_383 = !lean::is_exclusive(x_349);
if (x_383 == 0)
{
obj* x_384; obj* x_385; obj* x_386; 
x_384 = lean::cnstr_get(x_349, 0);
lean::dec(x_384);
x_385 = lean::cnstr_get(x_350, 0);
lean::inc(x_385);
lean::dec(x_350);
lean::cnstr_set(x_349, 0, x_347);
x_386 = lean::io_ref_get(x_3, x_349);
if (lean::obj_tag(x_386) == 0)
{
uint8 x_387; 
x_387 = !lean::is_exclusive(x_386);
if (x_387 == 0)
{
obj* x_388; obj* x_389; 
x_388 = lean::cnstr_get(x_386, 0);
lean::cnstr_set(x_386, 0, x_347);
x_389 = lean::io_ref_reset(x_3, x_386);
if (lean::obj_tag(x_389) == 0)
{
uint8 x_390; 
x_390 = !lean::is_exclusive(x_389);
if (x_390 == 0)
{
obj* x_391; obj* x_392; obj* x_393; 
x_391 = lean::cnstr_get(x_389, 0);
lean::dec(x_391);
lean::cnstr_set(x_389, 0, x_347);
x_392 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(x_346, x_388, x_385);
x_393 = lean::io_ref_set(x_3, x_392, x_389);
return x_393;
}
else
{
obj* x_394; obj* x_395; obj* x_396; obj* x_397; 
x_394 = lean::cnstr_get(x_389, 1);
lean::inc(x_394);
lean::dec(x_389);
x_395 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_395, 0, x_347);
lean::cnstr_set(x_395, 1, x_394);
x_396 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(x_346, x_388, x_385);
x_397 = lean::io_ref_set(x_3, x_396, x_395);
return x_397;
}
}
else
{
uint8 x_398; 
lean::dec(x_388);
lean::dec(x_385);
lean::dec(x_346);
x_398 = !lean::is_exclusive(x_389);
if (x_398 == 0)
{
return x_389;
}
else
{
obj* x_399; obj* x_400; obj* x_401; 
x_399 = lean::cnstr_get(x_389, 0);
x_400 = lean::cnstr_get(x_389, 1);
lean::inc(x_400);
lean::inc(x_399);
lean::dec(x_389);
x_401 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_401, 0, x_399);
lean::cnstr_set(x_401, 1, x_400);
return x_401;
}
}
}
else
{
obj* x_402; obj* x_403; obj* x_404; obj* x_405; 
x_402 = lean::cnstr_get(x_386, 0);
x_403 = lean::cnstr_get(x_386, 1);
lean::inc(x_403);
lean::inc(x_402);
lean::dec(x_386);
x_404 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_404, 0, x_347);
lean::cnstr_set(x_404, 1, x_403);
x_405 = lean::io_ref_reset(x_3, x_404);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; 
x_406 = lean::cnstr_get(x_405, 1);
lean::inc(x_406);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_407 = x_405;
} else {
 lean::dec_ref(x_405);
 x_407 = lean::box(0);
}
if (lean::is_scalar(x_407)) {
 x_408 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_408 = x_407;
}
lean::cnstr_set(x_408, 0, x_347);
lean::cnstr_set(x_408, 1, x_406);
x_409 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(x_346, x_402, x_385);
x_410 = lean::io_ref_set(x_3, x_409, x_408);
return x_410;
}
else
{
obj* x_411; obj* x_412; obj* x_413; obj* x_414; 
lean::dec(x_402);
lean::dec(x_385);
lean::dec(x_346);
x_411 = lean::cnstr_get(x_405, 0);
lean::inc(x_411);
x_412 = lean::cnstr_get(x_405, 1);
lean::inc(x_412);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_413 = x_405;
} else {
 lean::dec_ref(x_405);
 x_413 = lean::box(0);
}
if (lean::is_scalar(x_413)) {
 x_414 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_414 = x_413;
}
lean::cnstr_set(x_414, 0, x_411);
lean::cnstr_set(x_414, 1, x_412);
return x_414;
}
}
}
else
{
uint8 x_415; 
lean::dec(x_385);
lean::dec(x_346);
x_415 = !lean::is_exclusive(x_386);
if (x_415 == 0)
{
return x_386;
}
else
{
obj* x_416; obj* x_417; obj* x_418; 
x_416 = lean::cnstr_get(x_386, 0);
x_417 = lean::cnstr_get(x_386, 1);
lean::inc(x_417);
lean::inc(x_416);
lean::dec(x_386);
x_418 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_418, 0, x_416);
lean::cnstr_set(x_418, 1, x_417);
return x_418;
}
}
}
else
{
obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
x_419 = lean::cnstr_get(x_349, 1);
lean::inc(x_419);
lean::dec(x_349);
x_420 = lean::cnstr_get(x_350, 0);
lean::inc(x_420);
lean::dec(x_350);
x_421 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_421, 0, x_347);
lean::cnstr_set(x_421, 1, x_419);
x_422 = lean::io_ref_get(x_3, x_421);
if (lean::obj_tag(x_422) == 0)
{
obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; 
x_423 = lean::cnstr_get(x_422, 0);
lean::inc(x_423);
x_424 = lean::cnstr_get(x_422, 1);
lean::inc(x_424);
if (lean::is_exclusive(x_422)) {
 lean::cnstr_release(x_422, 0);
 lean::cnstr_release(x_422, 1);
 x_425 = x_422;
} else {
 lean::dec_ref(x_422);
 x_425 = lean::box(0);
}
if (lean::is_scalar(x_425)) {
 x_426 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_426 = x_425;
}
lean::cnstr_set(x_426, 0, x_347);
lean::cnstr_set(x_426, 1, x_424);
x_427 = lean::io_ref_reset(x_3, x_426);
if (lean::obj_tag(x_427) == 0)
{
obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; 
x_428 = lean::cnstr_get(x_427, 1);
lean::inc(x_428);
if (lean::is_exclusive(x_427)) {
 lean::cnstr_release(x_427, 0);
 lean::cnstr_release(x_427, 1);
 x_429 = x_427;
} else {
 lean::dec_ref(x_427);
 x_429 = lean::box(0);
}
if (lean::is_scalar(x_429)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_429;
}
lean::cnstr_set(x_430, 0, x_347);
lean::cnstr_set(x_430, 1, x_428);
x_431 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(x_346, x_423, x_420);
x_432 = lean::io_ref_set(x_3, x_431, x_430);
return x_432;
}
else
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; 
lean::dec(x_423);
lean::dec(x_420);
lean::dec(x_346);
x_433 = lean::cnstr_get(x_427, 0);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_427, 1);
lean::inc(x_434);
if (lean::is_exclusive(x_427)) {
 lean::cnstr_release(x_427, 0);
 lean::cnstr_release(x_427, 1);
 x_435 = x_427;
} else {
 lean::dec_ref(x_427);
 x_435 = lean::box(0);
}
if (lean::is_scalar(x_435)) {
 x_436 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_436 = x_435;
}
lean::cnstr_set(x_436, 0, x_433);
lean::cnstr_set(x_436, 1, x_434);
return x_436;
}
}
else
{
obj* x_437; obj* x_438; obj* x_439; obj* x_440; 
lean::dec(x_420);
lean::dec(x_346);
x_437 = lean::cnstr_get(x_422, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_422, 1);
lean::inc(x_438);
if (lean::is_exclusive(x_422)) {
 lean::cnstr_release(x_422, 0);
 lean::cnstr_release(x_422, 1);
 x_439 = x_422;
} else {
 lean::dec_ref(x_422);
 x_439 = lean::box(0);
}
if (lean::is_scalar(x_439)) {
 x_440 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_440 = x_439;
}
lean::cnstr_set(x_440, 0, x_437);
lean::cnstr_set(x_440, 1, x_438);
return x_440;
}
}
}
}
}
else
{
uint8 x_441; 
lean::dec(x_348);
lean::dec(x_346);
lean::dec(x_2);
x_441 = !lean::is_exclusive(x_349);
if (x_441 == 0)
{
return x_349;
}
else
{
obj* x_442; obj* x_443; obj* x_444; 
x_442 = lean::cnstr_get(x_349, 0);
x_443 = lean::cnstr_get(x_349, 1);
lean::inc(x_443);
lean::inc(x_442);
lean::dec(x_349);
x_444 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_444, 0, x_442);
lean::cnstr_set(x_444, 1, x_443);
return x_444;
}
}
}
else
{
obj* x_445; obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; 
x_445 = lean::cnstr_get(x_344, 0);
x_446 = lean::cnstr_get(x_344, 1);
lean::inc(x_446);
lean::inc(x_445);
lean::dec(x_344);
x_447 = lean::box(0);
x_448 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_448, 0, x_447);
lean::cnstr_set(x_448, 1, x_446);
x_449 = lean::cnstr_get(x_445, 0);
lean::inc(x_449);
lean::inc(x_449);
x_450 = l___private_init_lean_parser_parser_9__updateTokens(x_449, x_3, x_448);
if (lean::obj_tag(x_450) == 0)
{
obj* x_451; 
x_451 = lean::cnstr_get(x_449, 1);
lean::inc(x_451);
lean::dec(x_449);
switch (lean::obj_tag(x_451)) {
case 0:
{
obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; 
lean::dec(x_445);
x_452 = lean::cnstr_get(x_450, 1);
lean::inc(x_452);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 lean::cnstr_release(x_450, 1);
 x_453 = x_450;
} else {
 lean::dec_ref(x_450);
 x_453 = lean::box(0);
}
x_454 = l_Lean_Name_toString___closed__1;
x_455 = l_Lean_Name_toStringWithSep___main(x_454, x_2);
x_456 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_457 = lean::string_append(x_456, x_455);
lean::dec(x_455);
x_458 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_459 = lean::string_append(x_457, x_458);
if (lean::is_scalar(x_453)) {
 x_460 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_460 = x_453;
 lean::cnstr_set_tag(x_460, 1);
}
lean::cnstr_set(x_460, 0, x_459);
lean::cnstr_set(x_460, 1, x_452);
return x_460;
}
case 1:
{
obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
lean::dec(x_445);
x_461 = lean::cnstr_get(x_450, 1);
lean::inc(x_461);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 lean::cnstr_release(x_450, 1);
 x_462 = x_450;
} else {
 lean::dec_ref(x_450);
 x_462 = lean::box(0);
}
x_463 = l_Lean_Name_toString___closed__1;
x_464 = l_Lean_Name_toStringWithSep___main(x_463, x_2);
x_465 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1;
x_466 = lean::string_append(x_465, x_464);
lean::dec(x_464);
x_467 = l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2;
x_468 = lean::string_append(x_466, x_467);
if (lean::is_scalar(x_462)) {
 x_469 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_469 = x_462;
 lean::cnstr_set_tag(x_469, 1);
}
lean::cnstr_set(x_469, 0, x_468);
lean::cnstr_set(x_469, 1, x_461);
return x_469;
}
default: 
{
obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; 
lean::dec(x_2);
x_470 = lean::cnstr_get(x_450, 1);
lean::inc(x_470);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 lean::cnstr_release(x_450, 1);
 x_471 = x_450;
} else {
 lean::dec_ref(x_450);
 x_471 = lean::box(0);
}
x_472 = lean::cnstr_get(x_451, 0);
lean::inc(x_472);
lean::dec(x_451);
if (lean::is_scalar(x_471)) {
 x_473 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_473 = x_471;
}
lean::cnstr_set(x_473, 0, x_447);
lean::cnstr_set(x_473, 1, x_470);
x_474 = lean::io_ref_get(x_3, x_473);
if (lean::obj_tag(x_474) == 0)
{
obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; 
x_475 = lean::cnstr_get(x_474, 0);
lean::inc(x_475);
x_476 = lean::cnstr_get(x_474, 1);
lean::inc(x_476);
if (lean::is_exclusive(x_474)) {
 lean::cnstr_release(x_474, 0);
 lean::cnstr_release(x_474, 1);
 x_477 = x_474;
} else {
 lean::dec_ref(x_474);
 x_477 = lean::box(0);
}
if (lean::is_scalar(x_477)) {
 x_478 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_478 = x_477;
}
lean::cnstr_set(x_478, 0, x_447);
lean::cnstr_set(x_478, 1, x_476);
x_479 = lean::io_ref_reset(x_3, x_478);
if (lean::obj_tag(x_479) == 0)
{
obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; 
x_480 = lean::cnstr_get(x_479, 1);
lean::inc(x_480);
if (lean::is_exclusive(x_479)) {
 lean::cnstr_release(x_479, 0);
 lean::cnstr_release(x_479, 1);
 x_481 = x_479;
} else {
 lean::dec_ref(x_479);
 x_481 = lean::box(0);
}
if (lean::is_scalar(x_481)) {
 x_482 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_482 = x_481;
}
lean::cnstr_set(x_482, 0, x_447);
lean::cnstr_set(x_482, 1, x_480);
x_483 = l_List_foldl___main___at___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___spec__2(x_445, x_475, x_472);
x_484 = lean::io_ref_set(x_3, x_483, x_482);
return x_484;
}
else
{
obj* x_485; obj* x_486; obj* x_487; obj* x_488; 
lean::dec(x_475);
lean::dec(x_472);
lean::dec(x_445);
x_485 = lean::cnstr_get(x_479, 0);
lean::inc(x_485);
x_486 = lean::cnstr_get(x_479, 1);
lean::inc(x_486);
if (lean::is_exclusive(x_479)) {
 lean::cnstr_release(x_479, 0);
 lean::cnstr_release(x_479, 1);
 x_487 = x_479;
} else {
 lean::dec_ref(x_479);
 x_487 = lean::box(0);
}
if (lean::is_scalar(x_487)) {
 x_488 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_488 = x_487;
}
lean::cnstr_set(x_488, 0, x_485);
lean::cnstr_set(x_488, 1, x_486);
return x_488;
}
}
else
{
obj* x_489; obj* x_490; obj* x_491; obj* x_492; 
lean::dec(x_472);
lean::dec(x_445);
x_489 = lean::cnstr_get(x_474, 0);
lean::inc(x_489);
x_490 = lean::cnstr_get(x_474, 1);
lean::inc(x_490);
if (lean::is_exclusive(x_474)) {
 lean::cnstr_release(x_474, 0);
 lean::cnstr_release(x_474, 1);
 x_491 = x_474;
} else {
 lean::dec_ref(x_474);
 x_491 = lean::box(0);
}
if (lean::is_scalar(x_491)) {
 x_492 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_492 = x_491;
}
lean::cnstr_set(x_492, 0, x_489);
lean::cnstr_set(x_492, 1, x_490);
return x_492;
}
}
}
}
else
{
obj* x_493; obj* x_494; obj* x_495; obj* x_496; 
lean::dec(x_449);
lean::dec(x_445);
lean::dec(x_2);
x_493 = lean::cnstr_get(x_450, 0);
lean::inc(x_493);
x_494 = lean::cnstr_get(x_450, 1);
lean::inc(x_494);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 lean::cnstr_release(x_450, 1);
 x_495 = x_450;
} else {
 lean::dec_ref(x_450);
 x_495 = lean::box(0);
}
if (lean::is_scalar(x_495)) {
 x_496 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_496 = x_495;
}
lean::cnstr_set(x_496, 0, x_493);
lean::cnstr_set(x_496, 1, x_494);
return x_496;
}
}
}
else
{
uint8 x_497; 
lean::dec(x_2);
x_497 = !lean::is_exclusive(x_344);
if (x_497 == 0)
{
return x_344;
}
else
{
obj* x_498; obj* x_499; obj* x_500; 
x_498 = lean::cnstr_get(x_344, 0);
x_499 = lean::cnstr_get(x_344, 1);
lean::inc(x_499);
lean::inc(x_498);
lean::dec(x_344);
x_500 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_500, 0, x_498);
lean::cnstr_set(x_500, 1, x_499);
return x_500;
}
}
}
}
else
{
obj* x_501; 
lean::dec(x_335);
x_501 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_2, x_4);
return x_501;
}
}
}
else
{
obj* x_502; 
lean::dec(x_334);
lean::dec(x_13);
x_502 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_2, x_4);
return x_502;
}
}
default: 
{
obj* x_503; 
lean::dec(x_13);
x_503 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_2, x_4);
return x_503;
}
}
}
}
}
obj* l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_parser_11__addBuiltinParser___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_String_splitAux___main___closed__1;
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l___private_init_lean_parser_parser_11__addBuiltinParser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parser_11__addBuiltinParser___rarg), 1, 0);
return x_4;
}
}
obj* l___private_init_lean_parser_parser_11__addBuiltinParser___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_parser_11__addBuiltinParser(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_19; 
x_19 = l_Lean_Syntax_isMissing___main(x_6);
if (x_19 == 0)
{
uint8 x_20; 
lean::dec(x_5);
lean::dec(x_4);
x_20 = !lean::is_exclusive(x_8);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_8, 0);
lean::dec(x_21);
x_22 = l_Lean_Name_toString___closed__1;
x_23 = l_Lean_Name_toStringWithSep___main(x_22, x_1);
x_24 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_25 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_26 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_27 = lean::string_append(x_25, x_26);
lean::cnstr_set_tag(x_8, 1);
lean::cnstr_set(x_8, 0, x_27);
return x_8;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_8, 1);
lean::inc(x_28);
lean::dec(x_8);
x_29 = l_Lean_Name_toString___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_1);
x_31 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_32 = lean::string_append(x_31, x_30);
lean::dec(x_30);
x_33 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_34 = lean::string_append(x_32, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_28);
return x_35;
}
}
else
{
if (x_7 == 0)
{
uint8 x_36; 
lean::dec(x_5);
lean::dec(x_4);
x_36 = !lean::is_exclusive(x_8);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_37 = lean::cnstr_get(x_8, 0);
lean::dec(x_37);
x_38 = l_Lean_Name_toString___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_1);
x_40 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_41 = lean::string_append(x_40, x_39);
lean::dec(x_39);
x_42 = l_Lean_registerTagAttribute___lambda__5___closed__3;
x_43 = lean::string_append(x_41, x_42);
lean::cnstr_set_tag(x_8, 1);
lean::cnstr_set(x_8, 0, x_43);
return x_8;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_44 = lean::cnstr_get(x_8, 1);
lean::inc(x_44);
lean::dec(x_8);
x_45 = l_Lean_Name_toString___closed__1;
x_46 = l_Lean_Name_toStringWithSep___main(x_45, x_1);
x_47 = l_Lean_registerTagAttribute___lambda__5___closed__1;
x_48 = lean::string_append(x_47, x_46);
lean::dec(x_46);
x_49 = l_Lean_registerTagAttribute___lambda__5___closed__3;
x_50 = lean::string_append(x_48, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
}
else
{
uint8 x_52; 
lean::dec(x_1);
x_52 = !lean::is_exclusive(x_8);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_53 = lean::cnstr_get(x_8, 1);
x_54 = lean::cnstr_get(x_8, 0);
lean::dec(x_54);
x_55 = lean::box(0);
lean::inc(x_53);
lean::cnstr_set(x_8, 0, x_55);
lean::inc(x_5);
lean::inc(x_4);
x_56 = lean::environment_find_core(x_4, x_5);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_8);
lean::dec(x_5);
x_57 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1;
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_53);
x_9 = x_58;
goto block_18;
}
else
{
obj* x_59; obj* x_60; 
lean::dec(x_53);
x_59 = lean::cnstr_get(x_56, 0);
lean::inc(x_59);
lean::dec(x_56);
x_60 = l_Lean_ConstantInfo_type(x_59);
lean::dec(x_59);
switch (lean::obj_tag(x_60)) {
case 4:
{
obj* x_61; obj* x_62; uint8 x_63; 
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_62 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2;
x_63 = lean_name_dec_eq(x_61, x_62);
lean::dec(x_61);
if (x_63 == 0)
{
obj* x_64; 
x_64 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_8);
x_9 = x_64;
goto block_18;
}
else
{
obj* x_65; 
x_65 = lean::io_ref_get(x_2, x_8);
if (lean::obj_tag(x_65) == 0)
{
uint8 x_66; 
x_66 = !lean::is_exclusive(x_65);
if (x_66 == 0)
{
obj* x_67; obj* x_68; 
x_67 = lean::cnstr_get(x_65, 0);
lean::cnstr_set(x_65, 0, x_55);
x_68 = lean::io_ref_reset(x_2, x_65);
if (lean::obj_tag(x_68) == 0)
{
uint8 x_69; 
x_69 = !lean::is_exclusive(x_68);
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_68, 0);
lean::dec(x_70);
lean::cnstr_set(x_68, 0, x_55);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_5);
lean::cnstr_set(x_71, 1, x_67);
x_72 = lean::io_ref_set(x_2, x_71, x_68);
x_9 = x_72;
goto block_18;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_55);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_5);
lean::cnstr_set(x_75, 1, x_67);
x_76 = lean::io_ref_set(x_2, x_75, x_74);
x_9 = x_76;
goto block_18;
}
}
else
{
uint8 x_77; 
lean::dec(x_67);
lean::dec(x_5);
x_77 = !lean::is_exclusive(x_68);
if (x_77 == 0)
{
x_9 = x_68;
goto block_18;
}
else
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::cnstr_get(x_68, 0);
x_79 = lean::cnstr_get(x_68, 1);
lean::inc(x_79);
lean::inc(x_78);
lean::dec(x_68);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
x_9 = x_80;
goto block_18;
}
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_65, 0);
x_82 = lean::cnstr_get(x_65, 1);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_65);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_55);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::io_ref_reset(x_2, x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_85 = lean::cnstr_get(x_84, 1);
lean::inc(x_85);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_86 = x_84;
} else {
 lean::dec_ref(x_84);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_55);
lean::cnstr_set(x_87, 1, x_85);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_5);
lean::cnstr_set(x_88, 1, x_81);
x_89 = lean::io_ref_set(x_2, x_88, x_87);
x_9 = x_89;
goto block_18;
}
else
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_81);
lean::dec(x_5);
x_90 = lean::cnstr_get(x_84, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_84, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_92 = x_84;
} else {
 lean::dec_ref(x_84);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set(x_93, 1, x_91);
x_9 = x_93;
goto block_18;
}
}
}
else
{
uint8 x_94; 
lean::dec(x_5);
x_94 = !lean::is_exclusive(x_65);
if (x_94 == 0)
{
x_9 = x_65;
goto block_18;
}
else
{
obj* x_95; obj* x_96; obj* x_97; 
x_95 = lean::cnstr_get(x_65, 0);
x_96 = lean::cnstr_get(x_65, 1);
lean::inc(x_96);
lean::inc(x_95);
lean::dec(x_65);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_96);
x_9 = x_97;
goto block_18;
}
}
}
}
case 5:
{
obj* x_98; 
x_98 = lean::cnstr_get(x_60, 0);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 4)
{
obj* x_99; obj* x_100; obj* x_101; uint8 x_102; 
x_99 = lean::cnstr_get(x_60, 1);
lean::inc(x_99);
lean::dec(x_60);
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
lean::dec(x_98);
x_101 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3;
x_102 = lean_name_dec_eq(x_100, x_101);
lean::dec(x_100);
if (x_102 == 0)
{
obj* x_103; 
lean::dec(x_99);
x_103 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_8);
x_9 = x_103;
goto block_18;
}
else
{
if (lean::obj_tag(x_99) == 4)
{
obj* x_104; obj* x_105; uint8 x_106; 
x_104 = lean::cnstr_get(x_99, 0);
lean::inc(x_104);
lean::dec(x_99);
x_105 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4;
x_106 = lean_name_dec_eq(x_104, x_105);
lean::dec(x_104);
if (x_106 == 0)
{
obj* x_107; 
x_107 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_8);
x_9 = x_107;
goto block_18;
}
else
{
obj* x_108; 
x_108 = lean::io_ref_get(x_3, x_8);
if (lean::obj_tag(x_108) == 0)
{
uint8 x_109; 
x_109 = !lean::is_exclusive(x_108);
if (x_109 == 0)
{
obj* x_110; obj* x_111; 
x_110 = lean::cnstr_get(x_108, 0);
lean::cnstr_set(x_108, 0, x_55);
x_111 = lean::io_ref_reset(x_3, x_108);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_111);
if (x_112 == 0)
{
obj* x_113; obj* x_114; obj* x_115; 
x_113 = lean::cnstr_get(x_111, 0);
lean::dec(x_113);
lean::cnstr_set(x_111, 0, x_55);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_5);
lean::cnstr_set(x_114, 1, x_110);
x_115 = lean::io_ref_set(x_3, x_114, x_111);
x_9 = x_115;
goto block_18;
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_111, 1);
lean::inc(x_116);
lean::dec(x_111);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_55);
lean::cnstr_set(x_117, 1, x_116);
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_5);
lean::cnstr_set(x_118, 1, x_110);
x_119 = lean::io_ref_set(x_3, x_118, x_117);
x_9 = x_119;
goto block_18;
}
}
else
{
uint8 x_120; 
lean::dec(x_110);
lean::dec(x_5);
x_120 = !lean::is_exclusive(x_111);
if (x_120 == 0)
{
x_9 = x_111;
goto block_18;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_111, 0);
x_122 = lean::cnstr_get(x_111, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_111);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
x_9 = x_123;
goto block_18;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_124 = lean::cnstr_get(x_108, 0);
x_125 = lean::cnstr_get(x_108, 1);
lean::inc(x_125);
lean::inc(x_124);
lean::dec(x_108);
x_126 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_126, 0, x_55);
lean::cnstr_set(x_126, 1, x_125);
x_127 = lean::io_ref_reset(x_3, x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_128 = lean::cnstr_get(x_127, 1);
lean::inc(x_128);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 lean::cnstr_release(x_127, 1);
 x_129 = x_127;
} else {
 lean::dec_ref(x_127);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_55);
lean::cnstr_set(x_130, 1, x_128);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_5);
lean::cnstr_set(x_131, 1, x_124);
x_132 = lean::io_ref_set(x_3, x_131, x_130);
x_9 = x_132;
goto block_18;
}
else
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_124);
lean::dec(x_5);
x_133 = lean::cnstr_get(x_127, 0);
lean::inc(x_133);
x_134 = lean::cnstr_get(x_127, 1);
lean::inc(x_134);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 lean::cnstr_release(x_127, 1);
 x_135 = x_127;
} else {
 lean::dec_ref(x_127);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_133);
lean::cnstr_set(x_136, 1, x_134);
x_9 = x_136;
goto block_18;
}
}
}
else
{
uint8 x_137; 
lean::dec(x_5);
x_137 = !lean::is_exclusive(x_108);
if (x_137 == 0)
{
x_9 = x_108;
goto block_18;
}
else
{
obj* x_138; obj* x_139; obj* x_140; 
x_138 = lean::cnstr_get(x_108, 0);
x_139 = lean::cnstr_get(x_108, 1);
lean::inc(x_139);
lean::inc(x_138);
lean::dec(x_108);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_139);
x_9 = x_140;
goto block_18;
}
}
}
}
else
{
obj* x_141; 
lean::dec(x_99);
x_141 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_8);
x_9 = x_141;
goto block_18;
}
}
}
else
{
obj* x_142; 
lean::dec(x_98);
lean::dec(x_60);
x_142 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_8);
x_9 = x_142;
goto block_18;
}
}
default: 
{
obj* x_143; 
lean::dec(x_60);
x_143 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_8);
x_9 = x_143;
goto block_18;
}
}
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_144 = lean::cnstr_get(x_8, 1);
lean::inc(x_144);
lean::dec(x_8);
x_145 = lean::box(0);
lean::inc(x_144);
x_146 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_144);
lean::inc(x_5);
lean::inc(x_4);
x_147 = lean::environment_find_core(x_4, x_5);
if (lean::obj_tag(x_147) == 0)
{
obj* x_148; obj* x_149; 
lean::dec(x_146);
lean::dec(x_5);
x_148 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1;
x_149 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_144);
x_9 = x_149;
goto block_18;
}
else
{
obj* x_150; obj* x_151; 
lean::dec(x_144);
x_150 = lean::cnstr_get(x_147, 0);
lean::inc(x_150);
lean::dec(x_147);
x_151 = l_Lean_ConstantInfo_type(x_150);
lean::dec(x_150);
switch (lean::obj_tag(x_151)) {
case 4:
{
obj* x_152; obj* x_153; uint8 x_154; 
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
lean::dec(x_151);
x_153 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2;
x_154 = lean_name_dec_eq(x_152, x_153);
lean::dec(x_152);
if (x_154 == 0)
{
obj* x_155; 
x_155 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_146);
x_9 = x_155;
goto block_18;
}
else
{
obj* x_156; 
x_156 = lean::io_ref_get(x_2, x_146);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_156, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 x_159 = x_156;
} else {
 lean::dec_ref(x_156);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_145);
lean::cnstr_set(x_160, 1, x_158);
x_161 = lean::io_ref_reset(x_2, x_160);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_162 = lean::cnstr_get(x_161, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_163 = x_161;
} else {
 lean::dec_ref(x_161);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_145);
lean::cnstr_set(x_164, 1, x_162);
x_165 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_165, 0, x_5);
lean::cnstr_set(x_165, 1, x_157);
x_166 = lean::io_ref_set(x_2, x_165, x_164);
x_9 = x_166;
goto block_18;
}
else
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
lean::dec(x_157);
lean::dec(x_5);
x_167 = lean::cnstr_get(x_161, 0);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_161, 1);
lean::inc(x_168);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_169 = x_161;
} else {
 lean::dec_ref(x_161);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
lean::cnstr_set(x_170, 1, x_168);
x_9 = x_170;
goto block_18;
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
lean::dec(x_5);
x_171 = lean::cnstr_get(x_156, 0);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_156, 1);
lean::inc(x_172);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 x_173 = x_156;
} else {
 lean::dec_ref(x_156);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
lean::cnstr_set(x_174, 1, x_172);
x_9 = x_174;
goto block_18;
}
}
}
case 5:
{
obj* x_175; 
x_175 = lean::cnstr_get(x_151, 0);
lean::inc(x_175);
if (lean::obj_tag(x_175) == 4)
{
obj* x_176; obj* x_177; obj* x_178; uint8 x_179; 
x_176 = lean::cnstr_get(x_151, 1);
lean::inc(x_176);
lean::dec(x_151);
x_177 = lean::cnstr_get(x_175, 0);
lean::inc(x_177);
lean::dec(x_175);
x_178 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3;
x_179 = lean_name_dec_eq(x_177, x_178);
lean::dec(x_177);
if (x_179 == 0)
{
obj* x_180; 
lean::dec(x_176);
x_180 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_146);
x_9 = x_180;
goto block_18;
}
else
{
if (lean::obj_tag(x_176) == 4)
{
obj* x_181; obj* x_182; uint8 x_183; 
x_181 = lean::cnstr_get(x_176, 0);
lean::inc(x_181);
lean::dec(x_176);
x_182 = l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4;
x_183 = lean_name_dec_eq(x_181, x_182);
lean::dec(x_181);
if (x_183 == 0)
{
obj* x_184; 
x_184 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_146);
x_9 = x_184;
goto block_18;
}
else
{
obj* x_185; 
x_185 = lean::io_ref_get(x_3, x_146);
if (lean::obj_tag(x_185) == 0)
{
obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_186 = lean::cnstr_get(x_185, 0);
lean::inc(x_186);
x_187 = lean::cnstr_get(x_185, 1);
lean::inc(x_187);
if (lean::is_exclusive(x_185)) {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 x_188 = x_185;
} else {
 lean::dec_ref(x_185);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_145);
lean::cnstr_set(x_189, 1, x_187);
x_190 = lean::io_ref_reset(x_3, x_189);
if (lean::obj_tag(x_190) == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_191 = lean::cnstr_get(x_190, 1);
lean::inc(x_191);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 x_192 = x_190;
} else {
 lean::dec_ref(x_190);
 x_192 = lean::box(0);
}
if (lean::is_scalar(x_192)) {
 x_193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_193 = x_192;
}
lean::cnstr_set(x_193, 0, x_145);
lean::cnstr_set(x_193, 1, x_191);
x_194 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_194, 0, x_5);
lean::cnstr_set(x_194, 1, x_186);
x_195 = lean::io_ref_set(x_3, x_194, x_193);
x_9 = x_195;
goto block_18;
}
else
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_186);
lean::dec(x_5);
x_196 = lean::cnstr_get(x_190, 0);
lean::inc(x_196);
x_197 = lean::cnstr_get(x_190, 1);
lean::inc(x_197);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 x_198 = x_190;
} else {
 lean::dec_ref(x_190);
 x_198 = lean::box(0);
}
if (lean::is_scalar(x_198)) {
 x_199 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_199 = x_198;
}
lean::cnstr_set(x_199, 0, x_196);
lean::cnstr_set(x_199, 1, x_197);
x_9 = x_199;
goto block_18;
}
}
else
{
obj* x_200; obj* x_201; obj* x_202; obj* x_203; 
lean::dec(x_5);
x_200 = lean::cnstr_get(x_185, 0);
lean::inc(x_200);
x_201 = lean::cnstr_get(x_185, 1);
lean::inc(x_201);
if (lean::is_exclusive(x_185)) {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 x_202 = x_185;
} else {
 lean::dec_ref(x_185);
 x_202 = lean::box(0);
}
if (lean::is_scalar(x_202)) {
 x_203 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_203 = x_202;
}
lean::cnstr_set(x_203, 0, x_200);
lean::cnstr_set(x_203, 1, x_201);
x_9 = x_203;
goto block_18;
}
}
}
else
{
obj* x_204; 
lean::dec(x_176);
x_204 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_146);
x_9 = x_204;
goto block_18;
}
}
}
else
{
obj* x_205; 
lean::dec(x_175);
lean::dec(x_151);
x_205 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_146);
x_9 = x_205;
goto block_18;
}
}
default: 
{
obj* x_206; 
lean::dec(x_151);
x_206 = l___private_init_lean_parser_parser_8__throwUnexpectedParserType(x_5, x_146);
x_9 = x_206;
goto block_18;
}
}
}
}
}
}
block_18:
{
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_9, 0);
lean::dec(x_11);
lean::cnstr_set(x_9, 0, x_4);
return x_9;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8 x_14; 
lean::dec(x_4);
x_14 = !lean::is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_9, 0);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::io_mk_ref(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = lean::box(0);
x_9 = lean::io_mk_ref(x_8, x_4);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::cnstr_set(x_9, 0, x_7);
x_12 = lean::io_mk_ref(x_8, x_9);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::inc(x_14);
lean::inc(x_11);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed), 8, 3);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_11);
lean::closure_set(x_15, 2, x_14);
lean::inc(x_1);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_16, 0, x_1);
lean::inc(x_1);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_17, 0, x_1);
x_18 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_19 = l_Lean_registerTagAttribute___closed__5;
x_20 = l_Lean_registerTagAttribute___closed__6;
x_21 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_16);
lean::cnstr_set(x_21, 4, x_17);
lean::cnstr_set(x_21, 5, x_19);
lean::cnstr_set(x_21, 6, x_20);
lean::cnstr_set(x_21, 7, x_20);
lean::inc(x_21);
x_22 = l_Lean_registerAttribute(x_21, x_12);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::dec(x_24);
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_6);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set(x_25, 2, x_14);
lean::cnstr_set(x_25, 3, x_21);
lean::cnstr_set(x_22, 0, x_25);
return x_22;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_22, 1);
lean::inc(x_26);
lean::dec(x_22);
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_6);
lean::cnstr_set(x_27, 1, x_11);
lean::cnstr_set(x_27, 2, x_14);
lean::cnstr_set(x_27, 3, x_21);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8 x_29; 
lean::dec(x_21);
lean::dec(x_14);
lean::dec(x_11);
lean::dec(x_6);
x_29 = !lean::is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_22, 0);
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_22);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_33 = lean::cnstr_get(x_12, 0);
x_34 = lean::cnstr_get(x_12, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_12);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_7);
lean::cnstr_set(x_35, 1, x_34);
lean::inc(x_33);
lean::inc(x_11);
lean::inc(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed), 8, 3);
lean::closure_set(x_36, 0, x_1);
lean::closure_set(x_36, 1, x_11);
lean::closure_set(x_36, 2, x_33);
lean::inc(x_1);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_37, 0, x_1);
lean::inc(x_1);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_38, 0, x_1);
x_39 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_40 = l_Lean_registerTagAttribute___closed__5;
x_41 = l_Lean_registerTagAttribute___closed__6;
x_42 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_42, 0, x_1);
lean::cnstr_set(x_42, 1, x_39);
lean::cnstr_set(x_42, 2, x_36);
lean::cnstr_set(x_42, 3, x_37);
lean::cnstr_set(x_42, 4, x_38);
lean::cnstr_set(x_42, 5, x_40);
lean::cnstr_set(x_42, 6, x_41);
lean::cnstr_set(x_42, 7, x_41);
lean::inc(x_42);
x_43 = l_Lean_registerAttribute(x_42, x_35);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_45 = x_43;
} else {
 lean::dec_ref(x_43);
 x_45 = lean::box(0);
}
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_6);
lean::cnstr_set(x_46, 1, x_11);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_42);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_42);
lean::dec(x_33);
lean::dec(x_11);
lean::dec(x_6);
x_48 = lean::cnstr_get(x_43, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_43, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_50 = x_43;
} else {
 lean::dec_ref(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8 x_52; 
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_1);
x_52 = !lean::is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_12, 0);
x_54 = lean::cnstr_get(x_12, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_12);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_56 = lean::cnstr_get(x_9, 0);
x_57 = lean::cnstr_get(x_9, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_9);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_7);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::io_mk_ref(x_8, x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_59, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_62 = x_59;
} else {
 lean::dec_ref(x_59);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_7);
lean::cnstr_set(x_63, 1, x_61);
lean::inc(x_60);
lean::inc(x_56);
lean::inc(x_1);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed), 8, 3);
lean::closure_set(x_64, 0, x_1);
lean::closure_set(x_64, 1, x_56);
lean::closure_set(x_64, 2, x_60);
lean::inc(x_1);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_65, 0, x_1);
lean::inc(x_1);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_66, 0, x_1);
x_67 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_68 = l_Lean_registerTagAttribute___closed__5;
x_69 = l_Lean_registerTagAttribute___closed__6;
x_70 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_70, 0, x_1);
lean::cnstr_set(x_70, 1, x_67);
lean::cnstr_set(x_70, 2, x_64);
lean::cnstr_set(x_70, 3, x_65);
lean::cnstr_set(x_70, 4, x_66);
lean::cnstr_set(x_70, 5, x_68);
lean::cnstr_set(x_70, 6, x_69);
lean::cnstr_set(x_70, 7, x_69);
lean::inc(x_70);
x_71 = l_Lean_registerAttribute(x_70, x_63);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_71, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_73 = x_71;
} else {
 lean::dec_ref(x_71);
 x_73 = lean::box(0);
}
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_6);
lean::cnstr_set(x_74, 1, x_56);
lean::cnstr_set(x_74, 2, x_60);
lean::cnstr_set(x_74, 3, x_70);
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_72);
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_70);
lean::dec(x_60);
lean::dec(x_56);
lean::dec(x_6);
x_76 = lean::cnstr_get(x_71, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_71, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_78 = x_71;
} else {
 lean::dec_ref(x_71);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_56);
lean::dec(x_6);
lean::dec(x_1);
x_80 = lean::cnstr_get(x_59, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_59, 1);
lean::inc(x_81);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_82 = x_59;
} else {
 lean::dec_ref(x_59);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
lean::cnstr_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8 x_84; 
lean::dec(x_6);
lean::dec(x_1);
x_84 = !lean::is_exclusive(x_9);
if (x_84 == 0)
{
return x_9;
}
else
{
obj* x_85; obj* x_86; obj* x_87; 
x_85 = lean::cnstr_get(x_9, 0);
x_86 = lean::cnstr_get(x_9, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_9);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_88 = lean::cnstr_get(x_4, 0);
x_89 = lean::cnstr_get(x_4, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_4);
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
x_92 = lean::box(0);
x_93 = lean::io_mk_ref(x_92, x_91);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_93, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_96 = x_93;
} else {
 lean::dec_ref(x_93);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_90);
lean::cnstr_set(x_97, 1, x_95);
x_98 = lean::io_mk_ref(x_92, x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_100 = lean::cnstr_get(x_98, 1);
lean::inc(x_100);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_101 = x_98;
} else {
 lean::dec_ref(x_98);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_90);
lean::cnstr_set(x_102, 1, x_100);
lean::inc(x_99);
lean::inc(x_94);
lean::inc(x_1);
x_103 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed), 8, 3);
lean::closure_set(x_103, 0, x_1);
lean::closure_set(x_103, 1, x_94);
lean::closure_set(x_103, 2, x_99);
lean::inc(x_1);
x_104 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_104, 0, x_1);
lean::inc(x_1);
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_105, 0, x_1);
x_106 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_107 = l_Lean_registerTagAttribute___closed__5;
x_108 = l_Lean_registerTagAttribute___closed__6;
x_109 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_109, 0, x_1);
lean::cnstr_set(x_109, 1, x_106);
lean::cnstr_set(x_109, 2, x_103);
lean::cnstr_set(x_109, 3, x_104);
lean::cnstr_set(x_109, 4, x_105);
lean::cnstr_set(x_109, 5, x_107);
lean::cnstr_set(x_109, 6, x_108);
lean::cnstr_set(x_109, 7, x_108);
lean::inc(x_109);
x_110 = l_Lean_registerAttribute(x_109, x_102);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_111 = lean::cnstr_get(x_110, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_112 = x_110;
} else {
 lean::dec_ref(x_110);
 x_112 = lean::box(0);
}
x_113 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_113, 0, x_88);
lean::cnstr_set(x_113, 1, x_94);
lean::cnstr_set(x_113, 2, x_99);
lean::cnstr_set(x_113, 3, x_109);
if (lean::is_scalar(x_112)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_112;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_111);
return x_114;
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_109);
lean::dec(x_99);
lean::dec(x_94);
lean::dec(x_88);
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_110, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_117 = x_110;
} else {
 lean::dec_ref(x_110);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set(x_118, 1, x_116);
return x_118;
}
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
lean::dec(x_94);
lean::dec(x_88);
lean::dec(x_1);
x_119 = lean::cnstr_get(x_98, 0);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_98, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_121 = x_98;
} else {
 lean::dec_ref(x_98);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
lean::cnstr_set(x_122, 1, x_120);
return x_122;
}
}
else
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_88);
lean::dec(x_1);
x_123 = lean::cnstr_get(x_93, 0);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_93, 1);
lean::inc(x_124);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_125 = x_93;
} else {
 lean::dec_ref(x_93);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
uint8 x_127; 
lean::dec(x_1);
x_127 = !lean::is_exclusive(x_4);
if (x_127 == 0)
{
return x_4;
}
else
{
obj* x_128; obj* x_129; obj* x_130; 
x_128 = lean::cnstr_get(x_4, 0);
x_129 = lean::cnstr_get(x_4, 1);
lean::inc(x_129);
lean::inc(x_128);
lean::dec(x_4);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_129);
return x_130;
}
}
}
}
obj* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_7);
lean::dec(x_7);
x_10 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
}
obj* _init_l_Lean_Parser_mkBuiltinCommandParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinCommandParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkBuiltinCommandParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkBuiltinCommandParserAttr___closed__1;
x_3 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_mkBuiltinTermParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinTermParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkBuiltinTermParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkBuiltinTermParserAttr___closed__1;
x_3 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_mkBuiltinLevelParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinLevelParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkBuiltinLevelParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkBuiltinLevelParserAttr___closed__1;
x_3 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_mkBuiltinTestParserAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("builtinTestParser");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_mkBuiltinTestParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_mkBuiltinTestParserAttr___closed__1;
x_3 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_1);
return x_3;
}
}
obj* initialize_init_lean_position(obj*);
obj* initialize_init_lean_syntax(obj*);
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_attributes(obj*);
obj* initialize_init_lean_evalconst(obj*);
obj* initialize_init_lean_parser_trie(obj*);
obj* initialize_init_lean_parser_identifier(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_parser(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_position(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_syntax(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_evalconst(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_trie(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_identifier(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
lean::mark_persistent(l_Lean_Parser_maxPrec);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "maxPrec"), l_Lean_Parser_maxPrec);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenConfig"), "beq"), 2, l_Lean_Parser_TokenConfig_beq___boxed);
l_Lean_Parser_TokenConfig_HasBeq = _init_l_Lean_Parser_TokenConfig_HasBeq();
lean::mark_persistent(l_Lean_Parser_TokenConfig_HasBeq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "TokenConfig"), "HasBeq"), l_Lean_Parser_TokenConfig_HasBeq);
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
l_Lean_Parser_mkStrLitKind___closed__1 = _init_l_Lean_Parser_mkStrLitKind___closed__1();
lean::mark_persistent(l_Lean_Parser_mkStrLitKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkStrLitKind"), 1, l_Lean_Parser_mkStrLitKind);
w = l_Lean_Parser_mkStrLitKind(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_strLitKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_strLitKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLitKind"), l_Lean_Parser_strLitKind);
l_Lean_Parser_mkNumberKind___closed__1 = _init_l_Lean_Parser_mkNumberKind___closed__1();
lean::mark_persistent(l_Lean_Parser_mkNumberKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkNumberKind"), 1, l_Lean_Parser_mkNumberKind);
w = l_Lean_Parser_mkNumberKind(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_numberKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_numberKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "numberKind"), l_Lean_Parser_numberKind);
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "numberFn"), 2, l_Lean_Parser_numberFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "number"), 1, l_Lean_Parser_number___boxed);
l_Lean_Parser_strLitFn___rarg___closed__1 = _init_l_Lean_Parser_strLitFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_strLitFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLitFn"), 2, l_Lean_Parser_strLitFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "strLit"), 1, l_Lean_Parser_strLit___boxed);
l_Lean_Parser_identFn___rarg___closed__1 = _init_l_Lean_Parser_identFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_identFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "identFn"), 2, l_Lean_Parser_identFn___boxed);
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "indexed"), 1, l_Lean_Parser_indexed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "leadingParser"), 4, l_Lean_Parser_leadingParser___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "trailingParser"), 4, l_Lean_Parser_trailingParser);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "trailingLoop"), 5, l_Lean_Parser_trailingLoop___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "prattParser"), 4, l_Lean_Parser_prattParser);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkParserContext"), 4, l_Lean_Parser_mkParserContext);
l_Lean_Parser_runParser___closed__1 = _init_l_Lean_Parser_runParser___closed__1();
lean::mark_persistent(l_Lean_Parser_runParser___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "runParser"), 4, l_Lean_Parser_runParser);
l_Lean_Parser_BuiltinParserAttribute_Inhabited = _init_l_Lean_Parser_BuiltinParserAttribute_Inhabited();
lean::mark_persistent(l_Lean_Parser_BuiltinParserAttribute_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "BuiltinParserAttribute"), "Inhabited"), l_Lean_Parser_BuiltinParserAttribute_Inhabited);
l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1 = _init_l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1();
lean::mark_persistent(l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__1___closed__1);
l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1 = _init_l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1();
lean::mark_persistent(l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__1);
l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2 = _init_l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2();
lean::mark_persistent(l_List_mfoldl___main___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__3___closed__2);
l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1 = _init_l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1();
lean::mark_persistent(l_Lean_evalConst___at_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___spec__4___closed__1);
l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1 = _init_l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1();
lean::mark_persistent(l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "BuiltinParserAttribute"), "getTablesUnsafe"), 2, l_Lean_Parser_BuiltinParserAttribute_getTablesUnsafe___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "BuiltinParserAttribute"), "getTables"), 1, l_Lean_Parser_BuiltinParserAttribute_getTables___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "BuiltinParserAttribute"), "runParser"), 5, l_Lean_Parser_BuiltinParserAttribute_runParser___boxed);
l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1 = _init_l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1();
lean::mark_persistent(l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__1);
l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2 = _init_l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2();
lean::mark_persistent(l___private_init_lean_parser_parser_8__throwUnexpectedParserType___closed__2);
l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1 = _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1();
lean::mark_persistent(l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__1);
l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2 = _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2();
lean::mark_persistent(l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__2);
l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3 = _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3();
lean::mark_persistent(l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__3);
l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4 = _init_l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4();
lean::mark_persistent(l___private_init_lean_parser_parser_10__addBuiltinParserUnsafe___closed__4);
l_Lean_Parser_registerBuiltinParserAttribute___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1();
lean::mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "registerBuiltinParserAttribute"), 2, l_Lean_Parser_registerBuiltinParserAttribute);
l_Lean_Parser_mkBuiltinCommandParserAttr___closed__1 = _init_l_Lean_Parser_mkBuiltinCommandParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_mkBuiltinCommandParserAttr___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkBuiltinCommandParserAttr"), 1, l_Lean_Parser_mkBuiltinCommandParserAttr);
l_Lean_Parser_mkBuiltinTermParserAttr___closed__1 = _init_l_Lean_Parser_mkBuiltinTermParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_mkBuiltinTermParserAttr___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkBuiltinTermParserAttr"), 1, l_Lean_Parser_mkBuiltinTermParserAttr);
l_Lean_Parser_mkBuiltinLevelParserAttr___closed__1 = _init_l_Lean_Parser_mkBuiltinLevelParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_mkBuiltinLevelParserAttr___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkBuiltinLevelParserAttr"), 1, l_Lean_Parser_mkBuiltinLevelParserAttr);
w = l_Lean_Parser_mkBuiltinCommandParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinCommandParserAttr = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinCommandParserAttr);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinCommandParserAttr"), l_Lean_Parser_builtinCommandParserAttr);
w = l_Lean_Parser_mkBuiltinTermParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinTermParserAttr = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinTermParserAttr);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinTermParserAttr"), l_Lean_Parser_builtinTermParserAttr);
w = l_Lean_Parser_mkBuiltinLevelParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinLevelParserAttr = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinLevelParserAttr);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinLevelParserAttr"), l_Lean_Parser_builtinLevelParserAttr);
l_Lean_Parser_mkBuiltinTestParserAttr___closed__1 = _init_l_Lean_Parser_mkBuiltinTestParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_mkBuiltinTestParserAttr___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "mkBuiltinTestParserAttr"), 1, l_Lean_Parser_mkBuiltinTestParserAttr);
w = l_Lean_Parser_mkBuiltinTestParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinTestParserAttr = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinTestParserAttr);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinTestParserAttr"), l_Lean_Parser_builtinTestParserAttr);
return w;
}
