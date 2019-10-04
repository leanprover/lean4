// Lean compiler output
// Module: Init.Lean.Parser.Parser
// Imports: Init.Lean.Position Init.Lean.Syntax Init.Lean.ToExpr Init.Lean.Message Init.Lean.Environment Init.Lean.Attributes Init.Lean.Parser.Trie Init.Lean.Parser.Identifier Init.Lean.Compiler.InitAttr
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
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_1__expectedToString___main___closed__1;
uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_checkLeadingFn___closed__1;
lean_object* l_Lean_Parser_runParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ExceptT_lift___rarg___closed__1;
lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed___rarg___closed__1;
lean_object* l_Lean_Parser_mkAtomicInfo___closed__1;
lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_numberFnAux___closed__1;
lean_object* l_Lean_Parser_strLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_finishCommentBlock(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional___rarg(lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___lambda__2(lean_object*);
lean_object* l_Lean_Parser_TokenTableAttribute_inhabited___closed__2;
lean_object* l_Lean_Parser_quotedSymbolFn___boxed(lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg(lean_object*);
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString___closed__2;
lean_object* l_Lean_Parser_anyOfFn___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_insertToken___closed__4;
lean_object* l_Lean_Parser_sepBy1(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_strAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AttributeImpl_inhabited___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object*);
lean_object* l_Lean_Parser_hashAndthen(uint8_t);
lean_object* l_Lean_Parser_rawIdentFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserFn_inhabited___rarg(lean_object*);
lean_object* l_Lean_Parser_andthenFn___boxed(lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__7;
lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__4;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_builtinTokenTable;
lean_object* l_Lean_Parser_TokenConfig_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace___main(lean_object*, lean_object*);
uint8_t l_Lean_isIdRest(uint32_t);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__2;
lean_object* l_Lean_Parser_numLit___boxed(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
lean_object* l_Lean_Parser_orelseFn(uint8_t);
lean_object* l___private_Init_Lean_Parser_Parser_7__mkResult(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdEndEscape(uint32_t);
lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserAttribute_inhabited;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_octalNumberFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_anyOfFn___main___closed__1;
lean_object* l_Lean_Parser_anyOfFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Parser_longestMatchMkResult(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdent___boxed(lean_object*, lean_object*);
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2;
lean_object* l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserAttribute_inhabited___closed__3;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Fn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___elambda__2(lean_object*);
lean_object* l_Lean_Parser_numLit(uint8_t);
lean_object* l_Lean_Parser_decimalNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___closed__1;
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
extern lean_object* l_mjoin___rarg___closed__1;
lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__1;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
lean_object* l_Lean_Syntax_mfoldArgsAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookaheadFn(uint8_t);
lean_object* l_AssocList_replace___main___at_Lean_Parser_nodeInfo___elambda__1___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__4;
lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_Parser_ParserAttribute_runParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runBuiltinParser___rarg___boxed(lean_object*);
lean_object* l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserContextCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runBuiltinParser___rarg(lean_object*);
lean_object* l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Parser_quotedSymbol___elambda__1(uint8_t);
lean_object* l_Lean_Parser_mkParserContext(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_AssocList_mfoldl___main___at_Lean_Parser_nodeInfo___elambda__1___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runBuiltinParserUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unquotedSymbolFn(uint8_t, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Syntax_mforArgs(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
lean_object* l_Lean_Syntax_getOptionalIdent(lean_object*);
lean_object* l_Lean_Parser_symbolOrIdent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___closed__3;
lean_object* l_Lean_Parser_rawCh___elambda__1___rarg(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgs___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsAux(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___closed__2;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_5__tokenFnAux(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional(lean_object*);
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_Lean_Parser_rawFn___boxed(lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Parser_TokenTableAttribute_inhabited___closed__4;
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Parser_mkAtom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_string2basic___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDupsAux___main___at_Lean_Parser_addBuiltinLeadingParser___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_chFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushLeading___closed__2;
lean_object* l_Lean_Parser_Parser_inhabited(uint8_t);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Parser_strAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdent___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn(uint8_t);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4;
lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent___rarg(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Parser_mkTokenTableAttribute___spec__1(lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser___closed__1;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_uget(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_quotedSymbol___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh(uint8_t, uint32_t, uint8_t);
lean_object* l_mkHashMap___at_Lean_Parser_mkSyntaxNodeKindSetRef___spec__1(lean_object*);
lean_object* l_Lean_Parser_lookahead___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___lambda__2___closed__1;
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1;
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_appPrec;
lean_object* l_Lean_Parser_strLitFn___rarg___closed__1;
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux___main___closed__1;
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Parser_nodeInfo___elambda__1___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unquotedSymbolFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexDigitFn___closed__1;
lean_object* l_Array_uset(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_isIdCont___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFnAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLeadingFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional___rarg___boxed(lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Syntax_mforArgs___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___closed__3;
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_currLbp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitFnAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unquotedSymbol___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(lean_object*);
lean_object* l_Lean_Parser_charLit___closed__1;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_nodeFn___boxed(lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(uint8_t, lean_object*);
lean_object* l_Lean_Parser_hexNumberFn___closed__1;
lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5;
lean_object* l_Lean_Parser_quotedSymbol___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_Parser_node___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2;
lean_object* l_Lean_Parser_Error_Inhabited;
lean_object* l_Lean_Parser_optional(uint8_t, lean_object*);
lean_object* l_Lean_Parser_many1Indent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_HasToString___closed__1;
lean_object* l_Lean_Parser_whitespace___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_mkEmpty(lean_object*, lean_object*);
lean_object* l_Lean_Parser_anyOfFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_inhabited___closed__2;
lean_object* l_Lean_Parser_indexed___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toStr___closed__1;
lean_object* l_Lean_Parser_strLitFn(uint8_t, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgs(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_inhabited___boxed(lean_object*);
lean_object* l_Lean_Parser_tokenTableAttribute;
lean_object* l_Lean_Parser_fieldIdxFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionalFn___boxed(lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mforSepArgs___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore(uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserState___boxed(lean_object*);
lean_object* l_Lean_Parser_mkImportedTokenTable___rarg(lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_chFn___boxed(lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___main___rarg(lean_object*);
lean_object* l_Lean_Parser_Error_HasBeq___closed__1;
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_insertToken___closed__1;
lean_object* l_Lean_Parser_symbolOrIdent(uint8_t, lean_object*);
lean_object* l_Lean_Parser_withPosition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initAttr;
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(lean_object*);
lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__5;
lean_object* l_Lean_Parser_TokenMap_Inhabited(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_Lean_EnvExtensionState_inhabited;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(uint8_t);
lean_object* l_Lean_Parser_andthen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AttributeImpl_inhabited___lambda__5(lean_object*, lean_object*);
lean_object* l_Lean_Parser_currLbp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__1;
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hashOrelse___boxed(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
size_t lean_name_hash_usize(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_binNumberFn___closed__1;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFn(uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isNone___rarg(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__3;
lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object*);
uint8_t l_Lean_isIdBeginEscape(uint32_t);
lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_binNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___closed__2;
lean_object* l_Lean_Parser_TokenConfig_HasBeq;
lean_object* l_Lean_Parser_manyAux___main___closed__1;
lean_object* l_Lean_Parser_charLitFnAux___closed__1;
lean_object* l_Lean_Parser_runBuiltinParserUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_inhabited___closed__1;
lean_object* l_Lean_Parser_withPosition___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__1;
lean_object* l_Lean_Syntax_mforArgs___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_inhabited___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_manyAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_manyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__2(lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
uint8_t l_Lean_Syntax_isOfKind___rarg(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_Parser_optionalFn(uint8_t);
extern lean_object* l_Lean_FileMap_Inhabited___closed__1;
lean_object* l_Lean_Parser_TokenTableAttribute_inhabited;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_unquotedSymbol(uint8_t);
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(uint8_t);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFn___closed__1;
lean_object* l_IO_Prim_Ref_swap(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_insertNoWsToken___closed__1;
lean_object* l_Lean_Parser_charLit___boxed(lean_object*);
lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentFn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLeadingFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitFnAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbol___boxed(lean_object*);
lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_6__updateCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkIdent(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isIdCont(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldSepArgs___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Syntax_getArgs___rarg(lean_object*);
lean_object* l_Lean_Parser_ident(uint8_t);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Parser_tryFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AttributeImpl_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId___rarg(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__8;
lean_object* l_Lean_Parser_ParserFn_inhabited___rarg___boxed(lean_object*);
lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__2;
lean_object* l_Lean_Parser_sepByFn(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace___boxed(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdxFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Parser_Parser_4__isToken(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l_Lean_Parser_Error_Inhabited___closed__1;
lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_octalNumberFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent___rarg___boxed(lean_object*);
lean_object* l_Lean_Parser_strLit(uint8_t);
lean_object* l_Lean_Parser_hashOrelse(uint8_t);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFn___rarg___closed__1;
lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldSepArgs___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Parser_symbolNoWs(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_many___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___lambda__2___closed__2;
lean_object* l_Lean_Parser_strLitFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkTokenTableAttribute(lean_object*);
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___closed__1;
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Parser_unicodeSymbolFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__4___closed__3;
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6(lean_object*);
lean_object* l_Lean_Parser_runBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Parser_nodeInfo___elambda__1___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_octalNumberFn___closed__1;
lean_object* l_Lean_Parser_rawFn(uint8_t);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__1;
lean_object* l_Lean_Parser_tryFn___boxed(lean_object*);
lean_object* l_Lean_Parser_identFnAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbolFn(uint8_t);
extern lean_object* l___private_Init_Lean_Compiler_InitAttr_2__isUnitType___closed__2;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__1;
lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_HasToString___closed__1;
lean_object* l_ExceptT_Monad___rarg___lambda__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenConfig_toStr(lean_object*);
lean_object* l_Lean_Parser_symbolFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mforSepArgs(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFn___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushLeadingFn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_chFn___spec__1(uint32_t, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Parser_ident___closed__1;
lean_object* l_Lean_Syntax_foldSepArgs___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdent___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbol(uint8_t);
lean_object* l_Lean_Parser_TokenMap_insert(lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString___closed__3;
lean_object* l_Lean_Parser_insertToken___closed__5;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1(uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
lean_object* l_Lean_Parser_many1(uint8_t, lean_object*);
lean_object* l_Lean_Parser_trailingLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_insertToken___closed__2;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_checkTailWs(lean_object*);
lean_object* l_Lean_Parser_TokenTableAttribute_inhabited___closed__1;
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_strAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserAttribute_inhabited___closed__1;
lean_object* l_Lean_Parser_takeWhile1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_binNumberFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__5;
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenConfig_toStr___closed__1;
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
lean_object* l_IO_Prim_mkRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkImportedTokenTable(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFn_u2081___boxed(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__9;
lean_object* l_Lean_Parser_string2basic(uint8_t, lean_object*);
lean_object* l_Lean_Parser_many(uint8_t, lean_object*);
lean_object* l_Lean_Parser_rawIdent___boxed(lean_object*);
lean_object* l_Lean_Parser_finishCommentBlock___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object*);
lean_object* l_Lean_Parser_lookahead(uint8_t, lean_object*);
uint8_t l_Lean_Parser_TokenConfig_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___closed__2;
lean_object* l_Lean_Syntax_mfoldArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCApp(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLitFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParsingTables_inhabited___closed__1;
lean_object* l_Lean_Parser_unquotedSymbol___boxed(lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkSyntaxNodeKindSetRef___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___closed__4;
lean_object* l_Lean_Parser_runBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_octalNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
lean_object* l_Lean_Parser_try___boxed(lean_object*, lean_object*);
lean_object* l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(lean_object*);
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Lean_Parser_FirstTokens_HasToString;
lean_object* l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushLeading___closed__1;
lean_object* l_Lean_Parser_try(uint8_t, lean_object*);
lean_object* l_Lean_Parser_insertNoWsToken(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object*);
lean_object* l_Lean_Parser_chFn___rarg(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_EState_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_finishCommentBlock___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeFn(uint8_t);
lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_1__expectedToString___main(lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_hexNumberFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_object* l_Lean_Parser_identFn___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Position_Inhabited___closed__1;
lean_object* l_Lean_Parser_longestMatchStep(uint8_t);
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Parser_checkLeading(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___closed__1;
lean_object* l_Lean_Parser_optionalFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_hexNumberFn___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Parser_sepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsFn___closed__1;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn___boxed(lean_object*);
lean_object* l_Lean_Parser_fieldIdx___boxed(lean_object*);
lean_object* l_Lean_Parser_numLitFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_syntaxNodeKindSetRef;
uint8_t l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unquotedSymbol___elambda__1(uint8_t, lean_object*);
lean_object* l_Lean_Parser_andthenAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserContextCore(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolNoWsFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object*);
lean_object* l_Lean_Parser_ParserContextCore_inhabited___closed__1;
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_pop(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object*);
lean_object* l_Lean_Parser_symbolNoWsInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNone___rarg___boxed(lean_object*);
lean_object* l_Lean_Parser_strAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldSepArgs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Parser_registerParserAttribute___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Parser_runBuiltinParserUnsafe___closed__2;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__6;
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoopStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenConfig_HasToString;
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*);
lean_object* l_Lean_Parser_longestMatchFn_u2081___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFn_u2081(uint8_t);
lean_object* l_Lean_Parser_ParserState_setCache(lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object*);
lean_object* l_Lean_Parser_symbolAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7(lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object*);
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unquotedSymbol___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unquotedSymbolFn___rarg___closed__1;
extern lean_object* l_Lean_fieldIdxKind___closed__1;
lean_object* l_Lean_Parser_satisfySymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Trie_empty___closed__1;
uint8_t l_Char_isWhitespace(uint32_t);
lean_object* l_Lean_Parser_Error_toString___closed__1;
lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mforSepArgs___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
extern lean_object* l___private_Init_Lean_Compiler_InitAttr_1__getIOTypeArg___closed__2;
lean_object* l_Lean_Parser_charLit(uint8_t);
lean_object* l_Lean_Parser_manyAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_rawCh___elambda__1___spec__1(uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_chFn(uint8_t);
lean_object* l_Lean_Syntax_foldSepArgs(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux(uint8_t);
lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Error_beq(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6;
lean_object* l_Lean_Parser_strLit___closed__1;
lean_object* l_Lean_Syntax_mforSepArgs___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_Parser_getSyntaxNodeKinds___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_4__isToken___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_quotedSymbolFn___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString___closed__4;
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_TokenTableAttribute_inhabited___closed__3;
lean_object* l_Lean_Parser_symbolNoWs___boxed(lean_object*, lean_object*);
uint8_t l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___closed__5;
lean_object* l_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Parser_lookaheadFn___boxed(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserAttribute_inhabited___closed__4;
lean_object* l_Lean_Parser_identFn___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(lean_object*);
lean_object* l_Lean_Parser_TokenConfig_HasBeq___closed__1;
lean_object* l___private_Init_Lean_Parser_Parser_8__updateTokens(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_formatStx___main___rarg___closed__5;
lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_mkIdResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__3;
lean_object* l_Lean_Parser_quotedSymbol___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numberFnAux(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_ParserState_hasError(lean_object*);
lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_chFn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_Parser_manyAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__4;
lean_object* l_Lean_Parser_symbolNoWsInfo___closed__1;
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_quotedSymbolFn___spec__2(uint32_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1___boxed(lean_object*);
lean_object* l_Lean_Parser_nodeFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_sepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__1;
lean_object* l_Lean_Syntax_mfoldArgs___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParsingTables_inhabited;
lean_object* l_Lean_Parser_strLit___boxed(lean_object*);
lean_object* l_Lean_Parser_orelseFn___boxed(lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_HasBeq;
lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_Lean_Syntax_isMissing___rarg(lean_object*);
lean_object* l___private_Init_Lean_Parser_Parser_1__expectedToString(lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_Lean_Parser_rawIdent(uint8_t);
lean_object* l_Lean_Parser_mkBuiltinTokenTable(lean_object*);
lean_object* l_Lean_Parser_rawIdent___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident___boxed(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_rawCh___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object*);
lean_object* l_Lean_Parser_mkSyntaxNodeKindSetRef(lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_Parser_fieldIdxFn___closed__1;
lean_object* l_Lean_Parser_identFn(uint8_t, lean_object*);
lean_object* l_Lean_Parser_identFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolAux(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolCheckPrec(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_HasEmptyc(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_identFnAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushLeading;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__4;
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tryFn(uint8_t);
lean_object* l_Lean_Syntax_mfoldSepArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFn(uint8_t);
lean_object* l_Lean_Parser_rawIdent___closed__1;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_identFnAux___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore___elambda__1(uint8_t);
lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFn___rarg___closed__1;
lean_object* l_Lean_Parser_hexNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_updateSyntaxNodeKinds(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_runBuiltinParserUnsafe___closed__1;
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_binNumberFn___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx(uint8_t);
lean_object* l_Lean_Syntax_mfoldSepArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_insertToken___closed__3;
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserContextCore_inhabited;
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent___rarg(lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1;
lean_object* l_Lean_Parser_symbolInfo___closed__1;
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_insertToken(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenConfig_HasToString___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_Parser_nodeInfo___elambda__1___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_Inhabited___rarg___lambda__1(lean_object*);
uint8_t l_Lean_isIdFirst(uint32_t);
lean_object* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(lean_object*);
lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_mkImportedTokenTable___boxed(lean_object*);
lean_object* l_Lean_Parser_leadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolCheckPrec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLitFn(uint8_t, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharFn___closed__1;
lean_object* l_Lean_Syntax_mforArgs___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_Parser_withPosition(uint8_t, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh___elambda__1(uint8_t);
lean_object* l_IO_Prim_Ref_reset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserAttribute_inhabited___closed__2;
lean_object* l_Lean_Parser_checkColGe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Parser_quotedSymbolFn___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchStep___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___closed__2;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserContextCore_toParserContext(lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushLeadingFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserFn_inhabited___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_declareBuiltinParser___closed__6;
lean_object* l_Lean_Parser_fieldIdx___closed__1;
lean_object* l_Lean_Parser_hashAndthen___boxed(lean_object*);
lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Parser_ParserState_mkLongestNodeAlt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_anyOfFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object*);
lean_object* l_Lean_Parser_unquotedSymbolFn___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookaheadFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserFn_inhabited(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_HasToString;
lean_object* l_Lean_Parser_mkBuiltinParsingTablesRef(lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_mkIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_appPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1024u);
return x_1;
}
}
uint8_t l_Lean_Parser_TokenConfig_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_17 = lean_string_dec_eq(x_3, x_6);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_9 = x_19;
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_box(0);
x_9 = x_26;
goto block_16;
}
}
}
}
block_16:
{
lean_dec(x_9);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_nat_dec_eq(x_13, x_14);
return x_15;
}
}
}
}
}
lean_object* l_Lean_Parser_TokenConfig_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_TokenConfig_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_TokenConfig_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_TokenConfig_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_TokenConfig_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_TokenConfig_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_TokenConfig_toStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":none:");
return x_1;
}
}
lean_object* l_Lean_Parser_TokenConfig_toStr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Parser_TokenConfig_toStr___closed__1;
x_8 = lean_string_append(x_5, x_7);
x_9 = l_Nat_repr(x_6);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_panicWithPos___rarg___closed__2;
x_15 = lean_string_append(x_12, x_14);
x_16 = l_Nat_repr(x_13);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_panicWithPos___rarg___closed__2;
x_22 = lean_string_append(x_18, x_21);
x_23 = l_Nat_repr(x_19);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_panicWithPos___rarg___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Nat_repr(x_20);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
return x_28;
}
}
}
}
lean_object* _init_l_Lean_Parser_TokenConfig_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_TokenConfig_toStr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_TokenConfig_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_TokenConfig_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_initCacheForInput(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_ParserContextCore_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_Lean_FileMap_Inhabited___closed__1;
x_3 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_ParserContextCore_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParserContextCore_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Error_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Error_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Parser_Parser_1__expectedToString___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" or ");
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_1__expectedToString___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Parser_Parser_1__expectedToString___main___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l___private_Init_Lean_Parser_Parser_1__expectedToString___main(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
}
}
}
}
lean_object* l___private_Init_Lean_Parser_Parser_1__expectedToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Parser_Parser_1__expectedToString___main(x_1);
return x_2;
}
}
uint8_t l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_string_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1(x_7, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
}
}
}
lean_object* _init_l_Lean_Parser_Error_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Error_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("; ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Error_toString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_append___rarg(x_1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Error_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Error_toString___closed__2;
x_2 = l_Lean_Parser_Error_toString___closed__3;
x_3 = l_String_intercalate(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Error_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_String_splitAux___main___closed__1;
x_5 = lean_string_dec_eq(x_2, x_4);
x_6 = lean_box(0);
x_7 = l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1(x_3, x_6);
if (x_5 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l___private_Init_Lean_Parser_Parser_1__expectedToString___main(x_3);
x_10 = l_Lean_Parser_Error_toString___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = l_List_append___rarg(x_8, x_12);
x_14 = l_Lean_Parser_Error_toString___closed__2;
x_15 = l_String_intercalate(x_14, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_16 = l_List_append___rarg(x_8, x_6);
x_17 = l_Lean_Parser_Error_toString___closed__2;
x_18 = l_String_intercalate(x_17, x_16);
return x_18;
}
}
else
{
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l___private_Init_Lean_Parser_Parser_1__expectedToString___main(x_3);
x_20 = l_Lean_Parser_Error_toString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = l_List_append___rarg(x_6, x_22);
x_24 = l_Lean_Parser_Error_toString___closed__2;
x_25 = l_String_intercalate(x_24, x_23);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = l_Lean_Parser_Error_toString___closed__4;
return x_26;
}
}
}
}
lean_object* l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Error_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Error_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Error_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_HasToString___closed__1;
return x_1;
}
}
uint8_t l_Lean_Parser_Error_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_List_hasDecEq___main___at_Lean_Parser_Error_toString___spec__1(x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_Error_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_Error_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Error_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Error_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_Error_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_HasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_Error_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_String_splitAux___main___closed__1;
x_6 = lean_string_dec_eq(x_3, x_5);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_List_append___rarg(x_9, x_4);
if (x_6 == 0)
{
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_List_append___rarg(x_12, x_4);
if (x_6 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
uint8_t l_Lean_Parser_ParserState_hasError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserState_hasError(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserState_stackSize(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 3);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = l_Array_shrink___main___rarg(x_5, x_2);
x_9 = lean_box(0);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Array_shrink___main___rarg(x_10, x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_restore(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_setPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_ParserState_setCache(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_array_push(x_6, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_pop(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_array_pop(x_5);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Array_shrink___main___rarg(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = l_Array_shrink___main___rarg(x_6, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_shrinkStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_string_utf8_next(x_2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_string_utf8_next(x_2, x_3);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_String_splitAux___main___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Parser_Error_toString(x_5);
x_14 = l_Lean_mkErrorStringWithPos(x_10, x_11, x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 3);
lean_dec(x_7);
x_8 = lean_array_get_size(x_6);
lean_inc(x_3);
x_9 = l_Array_extract___rarg(x_6, x_3, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Array_shrink___main___rarg(x_6, x_3);
lean_dec(x_3);
x_12 = lean_array_push(x_11, x_10);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_array_get_size(x_13);
lean_inc(x_3);
x_17 = l_Array_extract___rarg(x_13, x_3, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_shrink___main___rarg(x_13, x_3);
lean_dec(x_3);
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_array_get_size(x_22);
x_26 = lean_nat_dec_eq(x_25, x_3);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_1, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 0);
lean_dec(x_31);
lean_inc(x_3);
x_32 = l_Array_extract___rarg(x_22, x_3, x_25);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Array_shrink___main___rarg(x_22, x_3);
lean_dec(x_3);
x_35 = lean_array_push(x_34, x_33);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
lean_inc(x_3);
x_36 = l_Array_extract___rarg(x_22, x_3, x_25);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_shrink___main___rarg(x_22, x_3);
lean_dec(x_3);
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_23);
lean_ctor_set(x_40, 2, x_24);
lean_ctor_set(x_40, 3, x_4);
return x_40;
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* l_Lean_Parser_ParserState_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_String_splitAux___main___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 3, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_String_splitAux___main___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_1, 3, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
}
lean_object* _init_l_Lean_Parser_ParserState_mkEOIError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end of input");
return x_1;
}
}
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_3 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_String_splitAux___main___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_1, 3, x_11);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_String_splitAux___main___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_18);
return x_19;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = l_String_splitAux___main___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Parser_ParserFn_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_ParserFn_inhabited(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_ParserFn_inhabited___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserFn_inhabited___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserFn_inhabited___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserFn_inhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_ParserFn_inhabited(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_List_append___rarg(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_append___rarg(x_3, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
default: 
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_List_append___rarg(x_10, x_12);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_append___rarg(x_10, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = l_List_append___rarg(x_17, x_19);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_List_append___rarg(x_17, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
default: 
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = l_List_append___rarg(x_24, x_26);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_List_append___rarg(x_24, x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_List_append___rarg(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_append___rarg(x_3, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
case 3:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_List_append___rarg(x_10, x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_append___rarg(x_10, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
return x_1;
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Parser_TokenConfig_toStr(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2(x_1, x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
x_11 = l_String_splitAux___main___closed__1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Parser_TokenConfig_toStr(x_12);
x_15 = 0;
x_16 = l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2(x_15, x_13);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("epsilon");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?");
return x_1;
}
}
lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_FirstTokens_toStr___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_6);
x_8 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Parser_FirstTokens_toStr___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_FirstTokens_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_toStr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_FirstTokens_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_FirstTokens_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_Parser_inhabited___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_Parser_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_ExceptT_lift___rarg___closed__1;
x_2 = l_mjoin___rarg___closed__1;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_Parser_inhabited___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Parser_inhabited___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_Parser_inhabited(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_Parser_inhabited___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Parser_inhabited___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Parser_inhabited___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_Parser_inhabited___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_Parser_inhabited(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_epsilonInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___elambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_epsilonInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_epsilonInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_epsilonInfo___closed__1;
x_2 = l_Lean_Parser_epsilonInfo___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_epsilonInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_epsilonInfo___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_pushLeadingFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_pushLeadingFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_pushLeadingFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_pushLeading___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_pushLeadingFn___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_pushLeading___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_pushLeading___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_pushLeading() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_pushLeading___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Parser_checkLeadingFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid leading token");
return x_1;
}
}
lean_object* l_Lean_Parser_checkLeadingFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_checkLeadingFn___closed__1;
x_8 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_7);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l_Lean_Parser_checkLeadingFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkLeadingFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_checkLeading(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLeadingFn___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_andthenAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_apply_2(x_2, x_3, x_5);
return x_7;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Lean_Parser_andthenFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_apply_3(x_2, x_3, x_4, x_6);
return x_8;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* l_Lean_Parser_andthenFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_andthenFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_andthenFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_andthenInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___elambda__1), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Parser_FirstTokens_seq(x_7, x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_andthen(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_andthenInfo(x_4, x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn___rarg), 5, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_andthen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_andthen(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_hashAndthen(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthen___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_hashAndthen___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_hashAndthen(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_nodeFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_apply_3(x_2, x_3, x_4, x_5);
x_9 = l_Lean_Parser_ParserState_mkNode(x_8, x_1, x_7);
return x_9;
}
}
lean_object* l_Lean_Parser_nodeFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_nodeFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_nodeFn(x_2);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_Parser_nodeInfo___elambda__1___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_name_hash_usize(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Parser_nodeInfo___elambda__1___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_Parser_nodeInfo___elambda__1___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_Parser_nodeInfo___elambda__1___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Parser_nodeInfo___elambda__1___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Parser_nodeInfo___elambda__1___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Parser_nodeInfo___elambda__1___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Parser_nodeInfo___elambda__1___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Parser_nodeInfo___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_name_hash_usize(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_Parser_nodeInfo___elambda__1___spec__3(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_Parser_nodeInfo___elambda__1___spec__6(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_name_hash_usize(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_Parser_nodeInfo___elambda__1___spec__3(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_Parser_nodeInfo___elambda__1___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_HashMapImp_insert___at_Lean_Parser_nodeInfo___elambda__1___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_nodeInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___elambda__2), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___elambda__1), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_node(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Parser_nodeInfo(x_2, x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_node___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_node(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_leadingNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_Parser_nodeInfo(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_trailingNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_Parser_nodeInfo(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn___rarg), 5, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_nat_dec_eq(x_6, x_3);
if (x_10 == 0)
{
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = l_Lean_Parser_Error_merge(x_2, x_9);
lean_ctor_set(x_4, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Parser_Error_merge(x_2, x_9);
lean_ctor_set(x_4, 0, x_17);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
lean_ctor_set(x_18, 3, x_4);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_nat_dec_eq(x_6, x_3);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_21 = x_1;
} else {
 lean_dec_ref(x_1);
 x_21 = lean_box(0);
}
x_22 = l_Lean_Parser_Error_merge(x_2, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (lean_is_scalar(x_21)) {
 x_24 = lean_alloc_ctor(0, 4, 0);
} else {
 x_24 = x_21;
}
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
lean_ctor_set(x_24, 3, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_mergeOrElseErrors(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_orelseFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_3(x_1, x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_apply_3(x_2, x_3, x_4, x_14);
x_16 = l_Lean_Parser_mergeOrElseErrors(x_15, x_11, x_8);
lean_dec(x_8);
return x_16;
}
}
}
}
lean_object* l_Lean_Parser_orelseFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_orelseFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_orelseFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_orelseInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_orelseInfo___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_orelseInfo___elambda__1), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Parser_FirstTokens_merge(x_7, x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_orelse(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_orelseInfo(x_4, x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn___rarg), 5, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_orelse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_orelse(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_hashOrelse(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_orelse___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_hashOrelse___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_hashOrelse(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_noFirstTokenInfo___elambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_noFirstTokenInfo___elambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_tryFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
lean_dec(x_5);
x_8 = lean_apply_3(x_1, x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = l_Array_shrink___main___rarg(x_11, x_7);
lean_dec(x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Array_shrink___main___rarg(x_15, x_7);
lean_dec(x_7);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_9);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_tryFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_tryFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_tryFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_try(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn___rarg), 4, 1);
lean_closure_set(x_5, 0, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_tryFn___rarg), 4, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_try___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_try(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_optionalFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_apply_3(x_1, x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_nullKind;
x_11 = l_Lean_Parser_ParserState_mkNode(x_8, x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_7);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_14 = l_Lean_nullKind;
x_15 = l_Lean_Parser_ParserState_mkNode(x_8, x_14, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
x_17 = l_Lean_nullKind;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_6);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_optionalFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_optionalFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_optionalFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_optionaInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optionaInfo___elambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_optionaInfo___elambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Parser_FirstTokens_toOptional(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_optional(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_optionaInfo(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn___rarg), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_optional___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_optional(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_lookaheadFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_apply_3(x_1, x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_10;
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
}
lean_object* l_Lean_Parser_lookaheadFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_lookaheadFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_lookaheadFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_lookahead(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn___rarg), 4, 1);
lean_closure_set(x_5, 0, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn___rarg), 4, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_lookahead___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_lookahead(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_manyAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'many' parser combinator application, parser did not consume anything");
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_3(x_2, x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (x_12 == 0)
{
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Parser_manyAux___main___closed__1;
x_15 = l_Lean_Parser_ParserState_mkUnexpectedError(x_9, x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
x_17 = lean_nat_dec_eq(x_8, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_manyAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_manyAux___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_manyAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_manyAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_manyAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_manyAux(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_manyFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = l_Lean_Parser_manyAux___main(x_1, x_2, x_3, x_4, x_5);
x_9 = l_Lean_nullKind;
x_10 = l_Lean_Parser_ParserState_mkNode(x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_Lean_Parser_manyFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_manyFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_many(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_noFirstTokenInfo(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn___boxed), 5, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_many___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_many(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_many1Fn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_3(x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Parser_manyAux___main(x_1, x_2, x_3, x_4, x_8);
x_11 = l_Lean_nullKind;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_8, x_13, x_7);
return x_14;
}
}
}
lean_object* l_Lean_Parser_many1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_many1Fn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_many1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn___boxed), 5, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Parser_many1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_many1(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_13 = lean_apply_3(x_2, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_7);
x_18 = lean_apply_3(x_3, x_7, x_8, x_13);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
{
uint8_t _tmp_5 = x_4;
lean_object* _tmp_8 = x_18;
x_6 = _tmp_5;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_Parser_ParserState_restore(x_18, x_16, x_17);
lean_dec(x_16);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_5);
return x_23;
}
}
else
{
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
if (x_6 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_24);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
lean_dec(x_11);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_5);
return x_30;
}
}
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main(x_10, x_2, x_3, x_11, x_5, x_12, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_2__sepByFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux(x_10, x_2, x_3, x_11, x_5, x_12, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Parser_sepByFn(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main(x_1, x_3, x_4, x_2, x_9, x_10, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Parser_sepByFn(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Parser_sepBy1Fn(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l___private_Init_Lean_Parser_Parser_2__sepByFnAux___main(x_1, x_3, x_4, x_2, x_9, x_10, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Parser_sepBy1Fn(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_1(x_10, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_sepByInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_sepByInfo___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_sepByInfo___elambda__1), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_1(x_10, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_sepBy1Info(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__1), 3, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__1), 3, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
}
}
lean_object* l_Lean_Parser_sepBy(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_sepByInfo(x_5, x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(x_1);
x_11 = lean_box(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 7, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* l_Lean_Parser_sepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_sepBy(x_5, x_2, x_3, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_sepBy1(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_sepBy1Info(x_5, x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(x_1);
x_11 = lean_box(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 7, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_sepBy1(x_5, x_2, x_3, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_satisfyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get(x_7, x_5);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Parser_ParserState_next(x_4, x_7, x_5);
lean_dec(x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
x_3 = x_12;
goto _start;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_takeWhileFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeWhileFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_takeWhileFn___spec__1(x_1, x_3, x_5);
return x_7;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Lean_Parser_takeWhile1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_takeWhile1Fn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_finishCommentBlock___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; uint8_t x_42; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
x_10 = 45;
x_42 = x_8 == x_10;
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = 0;
x_11 = x_43;
goto block_41;
}
else
{
uint8_t x_44; 
x_44 = 1;
x_11 = x_44;
goto block_41;
}
block_41:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 47;
x_13 = x_8 == x_12;
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_string_utf8_at_end(x_5, x_9);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = lean_string_utf8_get(x_5, x_9);
x_18 = x_17 == x_10;
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_1 = x_22;
x_3 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_1);
x_25 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_26 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = lean_string_utf8_at_end(x_5, x_9);
if (x_27 == 0)
{
uint32_t x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_string_utf8_get(x_5, x_9);
x_29 = 47;
x_30 = x_28 == x_29;
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_dec_eq(x_1, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_nat_sub(x_1, x_33);
lean_dec(x_1);
x_36 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_1 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_1);
x_39 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_40 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_1);
x_45 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_46 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_45);
return x_46;
}
}
}
lean_object* l_Lean_Parser_finishCommentBlock___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_8 = 10;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_whitespace___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; uint8_t x_36; 
x_9 = 45;
x_36 = x_7 == x_9;
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 0;
x_10 = x_37;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = 1;
x_10 = x_38;
goto block_35;
}
block_35:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; uint8_t x_25; 
x_11 = 47;
x_25 = x_7 == x_11;
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 0;
x_12 = x_26;
goto block_24;
}
else
{
uint8_t x_27; 
x_27 = 1;
x_12 = x_27;
goto block_24;
}
block_24:
{
if (x_12 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_14 = lean_string_utf8_get(x_4, x_13);
x_15 = x_14 == x_9;
if (x_15 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_string_utf8_next(x_4, x_13);
lean_dec(x_13);
x_17 = lean_string_utf8_get(x_4, x_16);
x_18 = x_17 == x_9;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Parser_ParserState_next(x_2, x_4, x_16);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Parser_finishCommentBlock___main(x_20, x_1, x_19);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
x_2 = x_21;
goto _start;
}
else
{
lean_dec(x_22);
return x_21;
}
}
else
{
lean_dec(x_16);
return x_2;
}
}
}
}
}
else
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_29 = lean_string_utf8_get(x_4, x_28);
x_30 = x_29 == x_9;
if (x_30 == 0)
{
lean_dec(x_28);
return x_2;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_Parser_ParserState_next(x_2, x_4, x_28);
lean_dec(x_28);
x_32 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(x_1, x_31);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
x_2 = x_32;
goto _start;
}
else
{
lean_dec(x_33);
return x_32;
}
}
}
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_2 = x_39;
goto _start;
}
}
else
{
lean_dec(x_5);
return x_2;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_whitespace___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_whitespace___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_whitespace___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_whitespace___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_whitespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc_n(x_1, 2);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_1);
x_10 = lean_string_utf8_extract(x_7, x_1, x_8);
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_8);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_Lean_Parser_whitespace___main(x_4, x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_inc(x_7);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
x_22 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_21);
return x_22;
}
}
}
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Parser_3__rawAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_3__rawAux___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Lean_Parser_Parser_3__rawAux(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_rawFn___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_3(x_1, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_6, x_2, x_3, x_4, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
lean_object* l_Lean_Parser_rawFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_rawFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_rawFn___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_rawFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_rawFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_chFn___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get(x_7, x_5);
x_10 = x_1 == x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = l_Lean_Parser_ParserState_next(x_4, x_7, x_5);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
x_13 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_chFn___rarg(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_String_splitAux___main___closed__1;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Char_HasRepr___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = l_Lean_Parser_satisfyFn___at_Lean_Parser_chFn___spec__1(x_1, x_11, x_4, x_5);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_6, x_2, x_3, x_4, x_12);
return x_14;
}
else
{
lean_dec(x_13);
lean_dec(x_6);
return x_12;
}
}
}
lean_object* l_Lean_Parser_chFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_chFn___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_chFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_satisfyFn___at_Lean_Parser_chFn___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_chFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Parser_chFn___rarg(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Parser_chFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_chFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_rawCh___elambda__1___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get(x_7, x_5);
x_10 = x_1 == x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = l_Lean_Parser_ParserState_next(x_4, x_7, x_5);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
x_13 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_rawCh___elambda__1___rarg(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_String_splitAux___main___closed__1;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Char_HasRepr___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = l_Lean_Parser_satisfyFn___at_Lean_Parser_rawCh___elambda__1___spec__1(x_1, x_11, x_4, x_5);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_6, x_2, x_3, x_4, x_12);
return x_14;
}
else
{
lean_dec(x_13);
lean_dec(x_6);
return x_12;
}
}
}
lean_object* l_Lean_Parser_rawCh___elambda__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_rawCh___elambda__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_rawCh(uint8_t x_1, uint32_t x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box_uint32(x_2);
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_rawCh___elambda__1___rarg___boxed), 5, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_Parser_inhabited___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_rawCh___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_satisfyFn___at_Lean_Parser_rawCh___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_rawCh___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Parser_rawCh___elambda__1___rarg(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_rawCh___elambda__1(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_rawCh___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_rawCh(x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_hexDigitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid hexadecimal numeral");
return x_1;
}
}
lean_object* l_Lean_Parser_hexDigitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_21; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_21 = l_Char_isDigit(x_7);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 97;
x_23 = x_22 <= x_7;
if (x_23 == 0)
{
x_9 = x_21;
goto block_20;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 102;
x_25 = x_7 <= x_24;
if (x_25 == 0)
{
x_9 = x_25;
goto block_20;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_26;
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_27;
}
block_20:
{
uint32_t x_10; uint8_t x_11; 
x_10 = 65;
x_11 = x_10 <= x_7;
if (x_11 == 0)
{
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = l_Lean_Parser_hexDigitFn___closed__1;
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_14;
}
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 70;
x_16 = x_7 <= x_15;
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_17 = l_Lean_Parser_hexDigitFn___closed__1;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_17);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_19;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_28 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_29 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_28);
return x_29;
}
}
}
lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_hexDigitFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_quotedCharFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid escape sequence");
return x_1;
}
}
lean_object* l_Lean_Parser_quotedCharFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; uint8_t x_50; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = 92;
x_50 = x_7 == x_8;
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = 0;
x_9 = x_51;
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = 1;
x_9 = x_52;
goto block_49;
}
block_49:
{
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; uint8_t x_45; 
x_10 = 34;
x_45 = x_7 == x_10;
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 0;
x_11 = x_46;
goto block_44;
}
else
{
uint8_t x_47; 
x_47 = 1;
x_11 = x_47;
goto block_44;
}
block_44:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 39;
x_13 = x_7 == x_12;
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 110;
x_15 = x_7 == x_14;
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 116;
x_17 = x_7 == x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; uint8_t x_37; 
x_18 = 120;
x_37 = x_7 == x_18;
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_19 = x_38;
goto block_36;
}
else
{
uint8_t x_39; 
x_39 = 1;
x_19 = x_39;
goto block_36;
}
block_36:
{
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 117;
x_21 = x_7 == x_20;
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = l_Lean_Parser_quotedCharFn___closed__1;
x_23 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_25 = l_Lean_Parser_hexDigitFn(x_1, x_24);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Parser_hexDigitFn(x_1, x_25);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_hexDigitFn(x_1, x_27);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Parser_hexDigitFn(x_1, x_29);
return x_31;
}
else
{
lean_dec(x_30);
return x_29;
}
}
else
{
lean_dec(x_28);
return x_27;
}
}
else
{
lean_dec(x_26);
return x_25;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_33 = l_Lean_Parser_hexDigitFn(x_1, x_32);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Parser_hexDigitFn(x_1, x_33);
return x_35;
}
else
{
lean_dec(x_34);
return x_33;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
return x_40;
}
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
return x_41;
}
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
return x_42;
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
return x_43;
}
}
}
else
{
lean_object* x_48; 
x_48 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
return x_48;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
x_53 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_54 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_53);
return x_54;
}
}
}
lean_object* l_Lean_Parser_quotedCharFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_quotedCharFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkNodeToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc_n(x_2, 2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_2);
x_9 = lean_string_utf8_extract(x_6, x_2, x_7);
x_10 = l_Lean_Parser_whitespace___main(x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_mkLit(x_1, x_9, x_14);
x_16 = l_Lean_Parser_ParserState_pushSyntax(x_10, x_15);
return x_16;
}
}
lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkNodeToken(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_charLitFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing end of character literal");
return x_1;
}
}
lean_object* l_Lean_Parser_charLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; uint8_t x_36; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_11 = 92;
x_36 = x_8 == x_11;
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 0;
x_12 = x_37;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = 1;
x_12 = x_38;
goto block_35;
}
block_35:
{
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_dec(x_3);
if (lean_obj_tag(x_13) == 0)
{
uint32_t x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_14 = lean_string_utf8_get(x_5, x_9);
x_15 = lean_string_utf8_next(x_5, x_9);
lean_dec(x_9);
x_16 = l_Lean_Parser_ParserState_setPos(x_10, x_15);
x_17 = 39;
x_18 = x_14 == x_17;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = l_Lean_Parser_charLitFnAux___closed__1;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_16, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_charLitKind;
x_22 = l_Lean_Parser_mkNodeToken(x_21, x_1, x_2, x_16);
return x_22;
}
}
else
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_3);
x_23 = l_Lean_Parser_quotedCharFn(x_2, x_10);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_string_utf8_get(x_5, x_25);
x_27 = lean_string_utf8_next(x_5, x_25);
lean_dec(x_25);
x_28 = l_Lean_Parser_ParserState_setPos(x_23, x_27);
x_29 = 39;
x_30 = x_26 == x_29;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = l_Lean_Parser_charLitFnAux___closed__1;
x_32 = l_Lean_Parser_ParserState_mkUnexpectedError(x_28, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_charLitKind;
x_34 = l_Lean_Parser_mkNodeToken(x_33, x_1, x_2, x_28);
return x_34;
}
}
else
{
lean_dec(x_24);
lean_dec(x_1);
return x_23;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_39 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_40 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_39);
return x_40;
}
}
}
lean_object* l_Lean_Parser_charLitFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_charLitFnAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_strLitFnAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_11 = 34;
x_12 = x_8 == x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 92;
x_14 = x_8 == x_13;
if (x_14 == 0)
{
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Parser_quotedCharFn(x_2, x_10);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_1);
return x_16;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_strLitKind;
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_1, x_2, x_10);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_21);
return x_22;
}
}
}
lean_object* l_Lean_Parser_strLitFnAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_strLitFnAux___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_strLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_strLitFnAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_strLitFnAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_8 = l_Char_isDigit(x_7);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_9;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_decimalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_4 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_2, x_3);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_string_utf8_get(x_6, x_7);
x_9 = 46;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_11 = l_Lean_numLitKind;
x_12 = l_Lean_Parser_mkNodeToken(x_11, x_1, x_2, x_4);
return x_12;
}
else
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_14 = lean_string_utf8_get(x_6, x_13);
x_15 = l_Char_isDigit(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_16 = l_Lean_numLitKind;
x_17 = l_Lean_Parser_mkNodeToken(x_16, x_1, x_2, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Parser_ParserState_setPos(x_4, x_13);
x_19 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_2, x_18);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_Parser_mkNodeToken(x_20, x_1, x_2, x_19);
return x_21;
}
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_decimalNumberFn___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_decimalNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_binNumberFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = 48;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 49;
x_12 = x_8 == x_11;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_1);
x_16 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_8 = 48;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 49;
x_11 = x_7 == x_10;
if (x_11 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_14;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_binNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binary number");
return x_1;
}
}
lean_object* l_Lean_Parser_binNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_binNumberFn___closed__1;
x_5 = l_Lean_Parser_satisfyFn___at_Lean_Parser_binNumberFn___spec__1(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(x_2, x_5);
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = l_Lean_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_5);
return x_11;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_binNumberFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_satisfyFn___at_Lean_Parser_binNumberFn___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_binNumberFn___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_binNumberFn___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_binNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_octalNumberFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = 48;
x_10 = x_9 <= x_8;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_11;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 55;
x_13 = x_8 <= x_12;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_1);
x_16 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_8 = 48;
x_9 = x_8 <= x_7;
if (x_9 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 55;
x_11 = x_7 <= x_10;
if (x_11 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_12;
goto _start;
}
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_octalNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("octal number");
return x_1;
}
}
lean_object* l_Lean_Parser_octalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_octalNumberFn___closed__1;
x_5 = l_Lean_Parser_satisfyFn___at_Lean_Parser_octalNumberFn___spec__1(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(x_2, x_5);
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = l_Lean_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_5);
return x_11;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_octalNumberFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_satisfyFn___at_Lean_Parser_octalNumberFn___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_octalNumberFn___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_octalNumberFn___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_octalNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_hexNumberFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; uint32_t x_31; uint8_t x_32; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_31 = 48;
x_32 = x_31 <= x_8;
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 0;
x_9 = x_33;
goto block_30;
}
else
{
uint32_t x_34; uint8_t x_35; 
x_34 = 57;
x_35 = x_8 <= x_34;
if (x_35 == 0)
{
x_9 = x_35;
goto block_30;
}
else
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_36;
}
}
block_30:
{
uint32_t x_10; uint8_t x_11; 
x_10 = 97;
x_11 = x_10 <= x_8;
if (x_11 == 0)
{
if (x_9 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 65;
x_13 = x_12 <= x_8;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 70;
x_16 = x_8 <= x_15;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_19;
}
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 102;
x_21 = x_8 <= x_20;
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 65;
x_23 = x_22 <= x_8;
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_4);
x_24 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_24;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 70;
x_26 = x_8 <= x_25;
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_4);
x_27 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_29;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
lean_dec(x_1);
x_37 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_38 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_37);
return x_38;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; uint32_t x_30; uint8_t x_31; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_30 = 48;
x_31 = x_30 <= x_7;
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 0;
x_8 = x_32;
goto block_29;
}
else
{
uint32_t x_33; uint8_t x_34; 
x_33 = 57;
x_34 = x_7 <= x_33;
if (x_34 == 0)
{
x_8 = x_34;
goto block_29;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_35;
goto _start;
}
}
block_29:
{
uint32_t x_9; uint8_t x_10; 
x_9 = 97;
x_10 = x_9 <= x_7;
if (x_10 == 0)
{
if (x_8 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 65;
x_12 = x_11 <= x_7;
if (x_12 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 70;
x_14 = x_7 <= x_13;
if (x_14 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_17;
goto _start;
}
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 102;
x_20 = x_7 <= x_19;
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 65;
x_22 = x_21 <= x_7;
if (x_22 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 70;
x_24 = x_7 <= x_23;
if (x_24 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_25;
goto _start;
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_27;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_hexNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hexadecimal number");
return x_1;
}
}
lean_object* l_Lean_Parser_hexNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_hexNumberFn___closed__1;
x_5 = l_Lean_Parser_satisfyFn___at_Lean_Parser_hexNumberFn___spec__1(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(x_2, x_5);
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = l_Lean_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_5);
return x_11;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_hexNumberFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_satisfyFn___at_Lean_Parser_hexNumberFn___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_hexNumberFn___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_hexNumberFn___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_hexNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_numberFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numeral");
return x_1;
}
}
lean_object* l_Lean_Parser_numberFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = 48;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Char_isDigit(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_Parser_numberFnAux___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
x_14 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; uint32_t x_16; uint32_t x_17; uint8_t x_18; 
x_15 = lean_string_utf8_next(x_4, x_5);
x_16 = lean_string_utf8_get(x_4, x_15);
x_17 = 98;
x_18 = x_16 == x_17;
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 66;
x_20 = x_16 == x_19;
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; uint8_t x_40; 
x_21 = 111;
x_40 = x_16 == x_21;
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 0;
x_22 = x_41;
goto block_39;
}
else
{
uint8_t x_42; 
x_42 = 1;
x_22 = x_42;
goto block_39;
}
block_39:
{
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 79;
x_24 = x_16 == x_23;
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 120;
x_26 = x_16 == x_25;
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 88;
x_28 = x_16 == x_27;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_ParserState_setPos(x_2, x_15);
x_30 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_32 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_34 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_36 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_38 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_44 = l_Lean_Parser_binNumberFn(x_5, x_1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_46 = l_Lean_Parser_binNumberFn(x_5, x_1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_5);
x_47 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_48 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_47);
return x_48;
}
}
}
lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_Parser_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = 46;
x_6 = x_4 == x_5;
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_string_utf8_next(x_1, x_3);
x_9 = lean_string_utf8_at_end(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = lean_string_utf8_get(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_isIdFirst(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isIdBeginEscape(x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = 0;
return x_14;
}
}
}
}
lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isIdCont(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Parser_Parser_4__isToken(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_nat_sub(x_2, x_1);
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_nat_dec_le(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Parser_Parser_4__isToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Parser_Parser_4__isToken(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_mkTokenAndFixPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("token");
return x_1;
}
}
lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_mkTokenAndFixPos___closed__1;
x_6 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_5, x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_8, 0);
lean_inc_n(x_1, 2);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 2, x_1);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_string_utf8_byte_size(x_12);
x_14 = lean_nat_add(x_1, x_13);
lean_dec(x_13);
lean_inc(x_14);
x_15 = l_Lean_Parser_ParserState_setPos(x_4, x_14);
x_16 = l_Lean_Parser_whitespace___main(x_3, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_inc(x_10);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_12);
x_21 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_22, 0);
lean_inc_n(x_1, 2);
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_nat_add(x_1, x_27);
lean_dec(x_27);
lean_inc(x_28);
x_29 = l_Lean_Parser_ParserState_setPos(x_4, x_28);
x_30 = l_Lean_Parser_whitespace___main(x_3, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_inc(x_24);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
x_36 = l_Lean_Parser_ParserState_pushSyntax(x_30, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_mkIdResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l___private_Init_Lean_Parser_Parser_4__isToken(x_1, x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_6);
x_11 = l_Lean_Parser_whitespace___main(x_4, x_5);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_inc_n(x_1, 2);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_1);
lean_inc(x_9);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_3);
x_20 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_20;
}
}
}
lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkIdResult(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_8 = l_Lean_isIdRest(x_7);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_9;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_5, x_3);
x_8 = l_Lean_isIdEndEscape(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Parser_ParserState_next(x_2, x_5, x_3);
lean_dec(x_3);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_identFnAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_12);
return x_13;
}
}
}
lean_object* _init_l_Lean_Parser_identFnAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing end of escaped identifier");
return x_1;
}
}
lean_object* l_Lean_Parser_identFnAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = lean_string_utf8_get(x_7, x_8);
x_11 = l_Lean_isIdBeginEscape(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isIdFirst(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_3);
x_13 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = l_Lean_Parser_ParserState_next(x_5, x_7, x_8);
x_15 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(x_4, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_string_utf8_extract(x_7, x_8, x_16);
lean_dec(x_8);
x_18 = lean_name_mk_string(x_3, x_17);
x_19 = l_Lean_Parser_isIdCont(x_7, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
x_20 = l_Lean_Parser_mkIdResult(x_1, x_2, x_18, x_4, x_15);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Parser_ParserState_next(x_15, x_7, x_16);
lean_dec(x_16);
x_3 = x_18;
x_5 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
lean_inc(x_23);
x_24 = l_Lean_Parser_ParserState_setPos(x_5, x_23);
x_25 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(x_4, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_Parser_identFnAux___main___closed__1;
x_28 = l_Lean_Parser_satisfyFn___at_Lean_Parser_identFnAux___main___spec__4(x_27, x_4, x_25);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_string_utf8_extract(x_7, x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
x_31 = lean_name_mk_string(x_3, x_30);
x_32 = l_Lean_Parser_isIdCont(x_7, x_28);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Parser_mkIdResult(x_1, x_2, x_31, x_4, x_28);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = l_Lean_Parser_ParserState_next(x_28, x_7, x_34);
lean_dec(x_34);
x_3 = x_31;
x_5 = x_35;
goto _start;
}
}
else
{
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_38 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_37);
return x_38;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeWhileFn___at_Lean_Parser_identFnAux___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_identFnAux___main___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_identFnAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_satisfyFn___at_Lean_Parser_identFnAux___main___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_identFnAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_identFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_5__tokenFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = 34;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 39;
x_10 = x_6 == x_9;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Char_isDigit(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l_Lean_Parser_Trie_matchPrefix___rarg(x_4, x_12, x_5);
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_identFnAux___main(x_5, x_14, x_15, x_1, x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_19 = l_Lean_Parser_charLitFnAux(x_5, x_1, x_18);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_21 = l_Lean_Parser_strLitFnAux___main(x_5, x_1, x_20);
lean_dec(x_1);
return x_21;
}
}
}
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = lean_array_get(x_2, x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_6__updateCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 3);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_4);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_2, 2, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_4);
lean_inc(x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_3);
return x_18;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_tokenFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_8, x_5);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l___private_Init_Lean_Parser_Parser_5__tokenFnAux(x_1, x_2);
x_11 = l___private_Init_Lean_Parser_Parser_6__updateCache(x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_12);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Parser_ParserState_setPos(x_13, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_1);
x_16 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_peekToken(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_13 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Parser_rawIdentFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_identFnAux___main(x_5, x_7, x_8, x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_rawIdentFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_3, x_4);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_2, x_5);
return x_13;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
else
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_2, x_5);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_2, x_5);
return x_15;
}
}
}
lean_object* l_Lean_Parser_symbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Lean_Parser_tokenFn(x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_string_dec_eq(x_12, x_1);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_6, x_7);
return x_14;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_6, x_7);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_9);
x_16 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_6, x_7);
return x_16;
}
}
}
lean_object* l_Lean_Parser_symbolFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_symbolFnAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_insertToken___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precedence mismatch for '");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_insertToken___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', previous: ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_insertToken___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", new: ");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_insertToken___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid empty symbol");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_insertToken___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_insertToken___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_insertToken(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_7 = l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(x_1, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_8);
x_10 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_9, x_3, x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_dec(x_16);
lean_ctor_set(x_13, 1, x_2);
x_17 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_13, x_3, x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_20);
x_22 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_21, x_3, x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
x_27 = l_Lean_Parser_insertToken___closed__1;
x_28 = lean_string_append(x_27, x_1);
lean_dec(x_1);
x_29 = l_Lean_Parser_insertToken___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Nat_repr(x_25);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = l_Lean_Parser_insertToken___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Nat_repr(x_24);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_3);
return x_38;
}
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_Parser_insertToken___closed__5;
return x_39;
}
}
}
lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_insertToken(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_symbolInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Parser_symbolInfo___closed__1;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_symbolFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Char_HasRepr___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = lean_string_append(x_6, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = l_Lean_Parser_tokenFn(x_3, x_4);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_string_dec_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_9, x_10);
return x_17;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
else
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_9, x_10);
return x_19;
}
}
}
lean_object* l_Lean_Parser_symbolFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_symbolFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_symbolFn___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_symbolFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_symbolAux(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_String_trim(x_2);
lean_inc(x_4);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_symbolAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_symbolAux(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_symbol(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_String_trim(x_2);
lean_inc(x_5);
x_6 = l_Lean_Parser_symbolInfo(x_5, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_symbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_symbol(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_symbolOrIdentFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_3, x_4);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_9)) {
case 2:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_string_dec_eq(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_string_utf8_extract(x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_string_dec_eq(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_1);
x_20 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_2);
x_21 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_1);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_21, x_22);
return x_23;
}
}
default: 
{
lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_1);
x_24 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_1);
x_25 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_25;
}
}
}
lean_object* l_Lean_Parser_symbolOrIdentFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Char_HasRepr___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
x_7 = l_Lean_Parser_symbolOrIdentFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
lean_object* l_Lean_Parser_symbolOrIdentInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolOrIdentInfo___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_symbolOrIdentInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_symbolOrIdentInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_symbolOrIdentInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_symbolOrIdentInfo___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_symbolOrIdentInfo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbolOrIdentInfo___elambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_symbolOrIdentInfo___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbolOrIdentInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolOrIdentInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
x_4 = l_Lean_Parser_symbolOrIdentInfo___closed__3;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_symbolOrIdentInfo___closed__4;
x_8 = l_Lean_Parser_symbolOrIdentInfo___closed__5;
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
lean_object* l_Lean_Parser_symbolOrIdentInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolOrIdentInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_symbolOrIdent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Char_HasRepr___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = lean_string_append(x_6, x_5);
x_8 = l_Lean_Parser_symbolOrIdentFnAux(x_1, x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Parser_symbolOrIdent(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_String_trim(x_2);
lean_inc(x_3);
x_4 = l_Lean_Parser_symbolOrIdentInfo(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_symbolOrIdent___lambda__1___boxed), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_symbolOrIdent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_symbolOrIdent___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_symbolOrIdent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_symbolOrIdent(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_strAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_string_utf8_at_end(x_9, x_7);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_1, x_3);
x_12 = lean_string_utf8_get(x_9, x_7);
x_13 = x_11 == x_12;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_3);
x_14 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_16 = l_Lean_Parser_ParserState_next(x_5, x_9, x_7);
lean_dec(x_7);
x_3 = x_15;
x_5 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_18;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Lean_Parser_strAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_strAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_strAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
uint8_t l_Lean_Parser_checkTailWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
}
lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_checkTailWs(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkWsBeforeFn(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_checkWsBefore___elambda__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBefore___elambda__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_checkWsBefore(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBefore___elambda__1___rarg___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_epsilonInfo;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkWsBefore___elambda__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_checkWsBefore___elambda__1(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_checkWsBefore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_checkWsBefore(x_3, x_2);
return x_4;
}
}
uint8_t l_Lean_Parser_checkTailNoWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
}
lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailNoWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_checkTailNoWs(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___rarg___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_epsilonInfo;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkNoWsBefore___elambda__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_checkNoWsBefore___elambda__1(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_checkNoWsBefore(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_insertNoWsToken___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(no whitespace) precedence mismatch for '");
return x_1;
}
}
lean_object* l_Lean_Parser_insertNoWsToken(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_7 = l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(x_1, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_2);
x_10 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_9, x_3, x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 2);
lean_dec(x_16);
lean_ctor_set(x_13, 2, x_2);
x_17 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_13, x_3, x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_2);
x_22 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_21, x_3, x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
x_27 = l_Lean_Parser_insertNoWsToken___closed__1;
x_28 = lean_string_append(x_27, x_1);
lean_dec(x_1);
x_29 = l_Lean_Parser_insertToken___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Nat_repr(x_25);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = l_Lean_Parser_insertToken___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Nat_repr(x_24);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_3);
return x_38;
}
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l_Lean_Parser_insertToken___closed__5;
return x_39;
}
}
}
lean_object* l_Lean_Parser_symbolNoWsInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolNoWsInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_insertNoWsToken(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_symbolNoWsInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbolNoWsInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolNoWsInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_symbolNoWsInfo___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Parser_symbolNoWsInfo___closed__1;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
lean_object* l_Lean_Parser_symbolNoWsInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolNoWsInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_symbolNoWsFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Parser_checkTailNoWs(x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Parser_strAux___main(x_1, x_2, x_11, x_4, x_5);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_n(x_9, 2);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_9);
x_15 = lean_string_utf8_byte_size(x_1);
x_16 = lean_nat_add(x_9, x_15);
lean_dec(x_15);
lean_inc(x_16);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_21 = l_Lean_Parser_ParserState_pushSyntax(x_12, x_20);
return x_21;
}
else
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
return x_12;
}
}
}
}
lean_object* l_Lean_Parser_symbolNoWsFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_symbolNoWsFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_symbolNoWsFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' without whitespaces around it");
return x_1;
}
}
lean_object* l_Lean_Parser_symbolNoWsFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Char_HasRepr___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Lean_Parser_symbolNoWsFn___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Parser_checkTailNoWs(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Parser_ParserState_mkError(x_4, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_strAux___main(x_1, x_8, x_14, x_3, x_4);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc_n(x_12, 2);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_12);
x_18 = lean_string_utf8_byte_size(x_1);
x_19 = lean_nat_add(x_12, x_18);
lean_dec(x_18);
lean_inc(x_19);
lean_inc(x_13);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_23);
return x_24;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_1);
return x_15;
}
}
}
}
lean_object* l_Lean_Parser_symbolNoWsFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_symbolNoWsFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_symbolNoWsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_String_trim(x_1);
lean_inc(x_3);
x_4 = l_Lean_Parser_symbolNoWsInfo(x_3, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_symbolNoWsFn___boxed), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_symbolNoWsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_symbolNoWsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_symbolNoWs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_String_trim(x_1);
lean_inc(x_4);
x_5 = l_Lean_Parser_symbolNoWsInfo(x_4, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbolNoWsFn___boxed), 4, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_symbolNoWs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_symbolNoWs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Lean_Parser_tokenFn(x_4, x_5);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_string_dec_eq(x_11, x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_string_dec_eq(x_11, x_2);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_mkErrorsAt(x_7, x_3, x_6);
return x_14;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = l_Lean_Parser_ParserState_mkErrorsAt(x_7, x_3, x_6);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = l_Lean_Parser_ParserState_mkErrorsAt(x_7, x_3, x_6);
return x_16;
}
}
}
lean_object* l_Lean_Parser_unicodeSymbolFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Parser_insertToken(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Parser_insertToken(x_2, x_3, x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Parser_unicodeSymbolInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___elambda__2), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_unicodeSymbolInfo___closed__1;
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_11);
return x_13;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_unicodeSymbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_unicodeSymbolFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', '");
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Char_HasRepr___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_Lean_Parser_unicodeSymbolFn___rarg___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = lean_string_append(x_10, x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_13, x_4, x_5);
return x_14;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_unicodeSymbolFn___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_unicodeSymbolFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_unicodeSymbol(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_String_trim(x_2);
x_6 = l_String_trim(x_3);
lean_inc(x_6);
lean_inc(x_5);
x_7 = l_Lean_Parser_unicodeSymbolInfo(x_5, x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn___rarg___boxed), 5, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_unicodeSymbol(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = l_Lean_Parser_tokenFn(x_7, x_8);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_string_dec_eq(x_15, x_1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_string_dec_eq(x_15, x_2);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_4, x_10);
return x_18;
}
else
{
lean_dec(x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_4, x_10);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_12);
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_11, x_4, x_10);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_4);
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_8, x_5);
return x_21;
}
}
}
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_unicodeSymbolCheckPrecFnAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("found '");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' as expected, but brackets are needed");
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = l_Char_HasRepr___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = lean_string_append(x_8, x_7);
x_10 = lean_string_append(x_7, x_2);
x_11 = lean_string_append(x_10, x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1;
x_16 = lean_string_append(x_15, x_1);
x_17 = l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lean_Parser_unicodeSymbolCheckPrecFnAux(x_1, x_2, x_3, x_14, x_18, x_4, x_5, x_6);
return x_19;
}
}
lean_object* l_Lean_Parser_unicodeSymbolCheckPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_unicodeSymbolCheckPrecFn(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Parser_unicodeSymbolCheckPrec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_String_trim(x_1);
x_5 = l_String_trim(x_2);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Parser_unicodeSymbolInfo(x_4, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolCheckPrecFn___boxed), 6, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_Parser_unicodeSymbolCheckPrec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_unicodeSymbolCheckPrec(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_mkAtomicInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkAtomicInfo___elambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Parser_mkAtomicInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkAtomicInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_mkAtomicInfo___closed__1;
x_8 = l_Lean_Parser_mkAtomicInfo___closed__2;
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAtomicInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_numLitFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_6);
lean_dec(x_6);
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_Syntax_isOfKind___rarg(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_numberFnAux___closed__1;
x_11 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_10, x_3);
return x_11;
}
else
{
lean_dec(x_3);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l_Lean_Parser_numberFnAux___closed__1;
x_13 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_12, x_3);
return x_13;
}
}
}
lean_object* l_Lean_Parser_numLitFn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_numLitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_numLitFn(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_numLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_numLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_numLit(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_numLit___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_numLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_numLit(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_strLitFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("string literal");
return x_1;
}
}
lean_object* l_Lean_Parser_strLitFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_6);
lean_dec(x_6);
x_8 = l_Lean_strLitKind;
x_9 = l_Lean_Syntax_isOfKind___rarg(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_strLitFn___rarg___closed__1;
x_11 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_10, x_3);
return x_11;
}
else
{
lean_dec(x_3);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l_Lean_Parser_strLitFn___rarg___closed__1;
x_13 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_12, x_3);
return x_13;
}
}
}
lean_object* l_Lean_Parser_strLitFn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_strLitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_strLitFn(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_strLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_strLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_strLit(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_strLit___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_strLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_strLit(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_charLitFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("character literal");
return x_1;
}
}
lean_object* l_Lean_Parser_charLitFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_6);
lean_dec(x_6);
x_8 = l_Lean_charLitKind;
x_9 = l_Lean_Syntax_isOfKind___rarg(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_charLitFn___rarg___closed__1;
x_11 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_10, x_3);
return x_11;
}
else
{
lean_dec(x_3);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l_Lean_Parser_charLitFn___rarg___closed__1;
x_13 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_12, x_3);
return x_13;
}
}
}
lean_object* l_Lean_Parser_charLitFn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_charLitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_charLitFn(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_charLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_charLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_charLit(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_charLit___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_charLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_charLit(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_identFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier");
return x_1;
}
}
lean_object* l_Lean_Parser_identFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_isIdent___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parser_identFn___rarg___closed__1;
x_10 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_9, x_3);
return x_10;
}
else
{
lean_dec(x_3);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_Parser_identFn___rarg___closed__1;
x_12 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_11, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Parser_identFn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_identFn___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_identFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_identFn(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_ident___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ident(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_identFn___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_ident___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_ident___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_ident(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_rawIdent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_rawIdentFn(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_rawIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_rawIdent___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_rawIdent(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = l_Lean_Parser_rawIdent___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_rawIdent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_rawIdent___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_rawIdent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_rawIdent(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get(x_7, x_5);
x_10 = x_1 == x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = l_Lean_Parser_ParserState_next(x_4, x_7, x_5);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
x_13 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_quotedSymbolFn___spec__2(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = x_8 == x_1;
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_3;
}
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
lean_object* _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quotedSymbol");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_quotedSymbolFn___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 96;
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = l_Lean_Parser_quotedSymbolFn___rarg___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_quotedSymbolFn___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_quotedSymbolFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_4 = 96;
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = l_Lean_Parser_quotedSymbolFn___rarg___closed__5;
x_24 = l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1(x_4, x_23, x_2, x_3);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_22, x_26, x_1, x_2, x_24);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_quotedSymbolFn___spec__2(x_4, x_2, x_27);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_29, x_26, x_1, x_2, x_30);
x_7 = x_32;
goto block_21;
}
else
{
lean_dec(x_31);
lean_dec(x_29);
x_7 = x_30;
goto block_21;
}
}
else
{
lean_dec(x_28);
x_7 = x_27;
goto block_21;
}
}
else
{
lean_dec(x_25);
lean_dec(x_22);
x_7 = x_24;
goto block_21;
}
block_21:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Lean_Parser_quotedSymbolFn___rarg___closed__5;
x_11 = l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1(x_4, x_10, x_2, x_7);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 1;
x_14 = l___private_Init_Lean_Parser_Parser_3__rawAux___rarg(x_9, x_13, x_1, x_2, x_11);
x_15 = l_Lean_Parser_quotedSymbolFn___rarg___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
x_17 = l_Lean_Parser_quotedSymbolFn___rarg___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_11, x_17, x_6);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_19 = l_Lean_Parser_quotedSymbolFn___rarg___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_7, x_19, x_6);
return x_20;
}
}
}
}
lean_object* l_Lean_Parser_quotedSymbolFn(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_quotedSymbolFn___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_satisfyFn___at_Lean_Parser_quotedSymbolFn___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_quotedSymbolFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_quotedSymbolFn___spec__2(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_quotedSymbolFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_quotedSymbolFn___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_quotedSymbolFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_quotedSymbolFn(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_quotedSymbol___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_quotedSymbolFn___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_quotedSymbol___elambda__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_quotedSymbol___elambda__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_quotedSymbol(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_Parser_inhabited___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_quotedSymbol___elambda__1___rarg___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_quotedSymbol___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_quotedSymbol___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_quotedSymbol___elambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_quotedSymbol___elambda__1(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_quotedSymbol___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_quotedSymbol(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_unquotedSymbolFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("symbol");
return x_1;
}
}
lean_object* l_Lean_Parser_unquotedSymbolFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_isIdent___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_strLitKind;
x_10 = l_Lean_Syntax_isOfKind___rarg(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_charLitKind;
x_12 = l_Lean_Syntax_isOfKind___rarg(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_numLitKind;
x_14 = l_Lean_Syntax_isOfKind___rarg(x_7, x_13);
lean_dec(x_7);
if (x_14 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Parser_unquotedSymbolFn___rarg___closed__1;
x_16 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_15, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_17 = l_Lean_Parser_unquotedSymbolFn___rarg___closed__1;
x_18 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_17, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_Parser_unquotedSymbolFn___rarg___closed__1;
x_20 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_19, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_21 = l_Lean_Parser_unquotedSymbolFn___rarg___closed__1;
x_22 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_21, x_3);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Parser_unquotedSymbolFn___rarg___closed__1;
x_24 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_23, x_3);
return x_24;
}
}
}
lean_object* l_Lean_Parser_unquotedSymbolFn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_unquotedSymbolFn___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_unquotedSymbolFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_unquotedSymbolFn(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_unquotedSymbol___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_unquotedSymbolFn___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_unquotedSymbol___elambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_unquotedSymbol___elambda__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_unquotedSymbol(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_unquotedSymbol___elambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_Parser_inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_unquotedSymbol___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_unquotedSymbol___elambda__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_unquotedSymbol___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_unquotedSymbol(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_fieldIdxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field index");
return x_1;
}
}
lean_object* l_Lean_Parser_fieldIdxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_get(x_5, x_3);
x_7 = l_Char_isDigit(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_fieldIdxFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_8, x_3);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 48;
x_11 = x_6 == x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_takeUntilFn___main___at_Lean_Parser_decimalNumberFn___spec__2(x_1, x_2);
x_13 = l_Lean_fieldIdxKind;
x_14 = l_Lean_Parser_mkNodeToken(x_13, x_3, x_1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Parser_fieldIdxFn___closed__1;
x_16 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_15, x_3);
return x_16;
}
}
}
}
lean_object* l_Lean_Parser_fieldIdxFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_fieldIdxFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_fieldIdx___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_fieldIdxFn(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_fieldIdx___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_fieldIdxKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_fieldIdx___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdx___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_fieldIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_fieldIdx___closed__1;
x_3 = l_Lean_Parser_fieldIdx___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_fieldIdx___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_fieldIdx___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_fieldIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_fieldIdx(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_string2basic(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = l_String_trim(x_2);
lean_inc(x_4);
x_5 = l_Lean_Parser_symbolInfo(x_4, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___rarg___boxed), 4, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_string2basic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_string2basic(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Array_shrink___main___rarg(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = l_Array_shrink___main___rarg(x_6, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepNewError(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 3);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = l_Array_shrink___main___rarg(x_6, x_2);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Array_shrink___main___rarg(x_10, x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_4);
return x_13;
}
}
}
lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_keepPrevError(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Lean_Parser_Error_beq(x_3, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = l_Array_shrink___main___rarg(x_5, x_2);
x_17 = l_Lean_Parser_Error_merge(x_3, x_9);
lean_ctor_set(x_4, 0, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = l_Array_shrink___main___rarg(x_5, x_2);
x_19 = l_Lean_Parser_Error_merge(x_3, x_9);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_7);
lean_ctor_set(x_20, 3, x_4);
return x_20;
}
}
else
{
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_1;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_Parser_Error_beq(x_3, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_23 = x_1;
} else {
 lean_dec_ref(x_1);
 x_23 = lean_box(0);
}
x_24 = l_Array_shrink___main___rarg(x_5, x_2);
x_25 = l_Lean_Parser_Error_merge(x_3, x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 4, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_7);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
else
{
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_1;
}
}
}
}
}
lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mergeErrors(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_mkLongestNodeAlt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_eq(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
lean_inc(x_2);
x_16 = l_Array_extract___rarg(x_3, x_2, x_6);
lean_dec(x_6);
x_17 = l_Lean_nullKind;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_shrink___main___rarg(x_3, x_2);
lean_dec(x_2);
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_box(0);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
lean_inc(x_2);
x_22 = l_Array_extract___rarg(x_3, x_2, x_6);
lean_dec(x_6);
x_23 = l_Lean_nullKind;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_shrink___main___rarg(x_3, x_2);
lean_dec(x_2);
x_26 = lean_array_push(x_25, x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_5);
lean_ctor_set(x_28, 3, x_27);
return x_28;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_1, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_dec(x_33);
x_34 = lean_box(0);
x_35 = lean_array_push(x_3, x_34);
x_36 = lean_box(0);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_array_push(x_3, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_4);
lean_ctor_set(x_40, 2, x_5);
lean_ctor_set(x_40, 3, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_4);
x_7 = l_Array_shrink___main___rarg(x_4, x_2);
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_box(0);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_10);
x_14 = l_Array_shrink___main___rarg(x_10, x_2);
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_1, x_3);
x_5 = l_Lean_Parser_ParserState_keepLatest(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_replaceLongest(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_longestMatchStep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = l_Lean_Parser_ParserState_restore(x_6, x_10, x_2);
x_12 = lean_apply_3(x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_lt(x_8, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_14, x_8);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
x_17 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_12, x_10);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_restore(x_12, x_10, x_8);
lean_dec(x_10);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_8);
x_19 = l_Lean_Parser_ParserState_replaceLongest(x_12, x_1, x_10);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_20 = l_Lean_Parser_ParserState_restore(x_12, x_10, x_8);
lean_dec(x_10);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_12, 3);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_22 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_12, x_1);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_8, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_lt(x_24, x_8);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
x_27 = l_Lean_Parser_ParserState_mergeErrors(x_12, x_10, x_23);
lean_dec(x_10);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_23);
x_28 = l_Lean_Parser_ParserState_keepPrevError(x_12, x_10, x_8, x_7);
lean_dec(x_10);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
x_29 = l_Lean_Parser_ParserState_keepNewError(x_12, x_10);
lean_dec(x_10);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Parser_longestMatchStep(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_longestMatchStep___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_longestMatchStep(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_choiceKind;
x_10 = l_Lean_Parser_ParserState_mkNode(x_2, x_9, x_1);
return x_10;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Lean_Parser_longestMatchFnAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_8 = l_Lean_Parser_longestMatchMkResult(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Parser_longestMatchStep___rarg(x_2, x_3, x_11, x_5, x_6, x_7);
x_4 = x_10;
x_7 = x_12;
goto _start;
}
}
}
lean_object* l_Lean_Parser_longestMatchFnAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Parser_longestMatchFnAux___main(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Parser_longestMatchFnAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_longestMatchFnAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Parser_longestMatchFnAux(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Parser_longestMatchFn_u2081___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_apply_3(x_1, x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_7, x_6);
return x_9;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Parser_longestMatchFn_u2081(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_longestMatchFn_u2081___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_longestMatchFn_u2081___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_longestMatchFn_u2081(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_longestMatchFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("longestMatch: empty list");
return x_1;
}
}
lean_object* l_Lean_Parser_longestMatchFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = l_Lean_Parser_longestMatchFn___closed__1;
x_7 = l_Lean_Parser_ParserState_mkError(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Parser_longestMatchFn_u2081___rarg(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_3(x_16, x_3, x_4, x_5);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_14);
x_19 = l_Lean_Parser_ParserState_mkLongestNodeAlt(x_17, x_14);
x_20 = l_Lean_Parser_longestMatchFnAux___main(x_1, x_14, x_15, x_8, x_3, x_4, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_21 = l_Lean_Parser_ParserState_shrinkStack(x_17, x_14);
x_22 = l_Lean_Parser_longestMatchFnAux___main(x_1, x_14, x_15, x_8, x_3, x_4, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Lean_Parser_longestMatchFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_longestMatchFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_anyOfFn___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anyOf: empty list");
return x_1;
}
}
lean_object* l_Lean_Parser_anyOfFn___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = l_Lean_Parser_anyOfFn___main___closed__1;
x_7 = l_Lean_Parser_ParserState_mkError(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_3(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_3(x_13, x_3, x_4, x_5);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_20, x_16);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_16);
x_22 = l_Lean_Parser_ParserState_restore(x_17, x_15, x_16);
lean_dec(x_15);
x_23 = l_Lean_Parser_anyOfFn___main(x_1, x_8, x_3, x_4, x_22);
x_24 = l_Lean_Parser_mergeOrElseErrors(x_23, x_19, x_16);
lean_dec(x_16);
return x_24;
}
}
}
}
}
}
lean_object* l_Lean_Parser_anyOfFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_anyOfFn___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_anyOfFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_anyOfFn___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_anyOfFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_anyOfFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_checkColGeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Lean_FileMap_toPosition(x_6, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_nat_dec_le(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Parser_ParserState_mkError(x_4, x_2);
return x_11;
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l_Lean_Parser_checkColGeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkColGeFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_checkColGe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_nat_dec_le(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_12;
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Lean_Parser_checkColGe(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGe___lambda__1___boxed), 5, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_Parser_inhabited___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_checkColGe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_checkColGe___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_checkColGe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_checkColGe(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_withPosition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Lean_FileMap_toPosition(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_3(x_10, x_2, x_3, x_4);
return x_11;
}
}
lean_object* l_Lean_Parser_withPosition(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Position_Inhabited___closed__1;
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_dec(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lambda__1), 4, 1);
lean_closure_set(x_7, 0, x_2);
lean_ctor_set(x_4, 1, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lambda__1), 4, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_withPosition___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_withPosition(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_FileMap_toPosition(x_30, x_12);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_dec_le(x_4, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_3);
x_34 = l_Lean_Parser_ParserState_mkError(x_8, x_3);
x_13 = x_34;
goto block_28;
}
else
{
x_13 = x_8;
goto block_28;
}
block_28:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_3(x_9, x_6, x_7, x_13);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
if (x_18 == 0)
{
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Parser_manyAux___main___closed__1;
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_15, x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
x_23 = lean_nat_dec_eq(x_12, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_15;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_Parser_ParserState_restore(x_15, x_11, x_12);
lean_dec(x_11);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_12, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
lean_dec(x_11);
return x_27;
}
}
}
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_FileMap_toPosition(x_30, x_12);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_nat_dec_le(x_4, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_3);
x_34 = l_Lean_Parser_ParserState_mkError(x_8, x_3);
x_13 = x_34;
goto block_28;
}
else
{
x_13 = x_8;
goto block_28;
}
block_28:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_3(x_9, x_6, x_7, x_13);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
if (x_18 == 0)
{
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Parser_manyAux___main___closed__1;
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_15, x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
x_23 = lean_nat_dec_eq(x_12, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_15;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_Parser_ParserState_restore(x_15, x_11, x_12);
lean_dec(x_11);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_eq(x_12, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_ParserState_restore(x_13, x_11, x_12);
lean_dec(x_11);
return x_27;
}
}
}
}
}
lean_object* l_Lean_Parser_many1Indent___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_16 = l_Lean_Parser_ParserState_mkError(x_6, x_2);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_5);
lean_inc(x_4);
x_18 = lean_apply_3(x_12, x_4, x_5, x_16);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__1(x_3, x_1, x_2, x_11, x_3, x_4, x_5, x_18);
lean_dec(x_11);
x_21 = l_Lean_nullKind;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_18, x_23, x_14);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_nullKind;
x_26 = l_Lean_Parser_ParserState_mkNode(x_16, x_25, x_14);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_6, 3);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_inc(x_5);
lean_inc(x_4);
x_28 = lean_apply_3(x_12, x_4, x_5, x_6);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__2(x_3, x_1, x_2, x_11, x_3, x_4, x_5, x_28);
lean_dec(x_11);
x_31 = l_Lean_nullKind;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_14);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_nullKind;
x_34 = l_Lean_Parser_ParserState_mkNode(x_28, x_33, x_14);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_nullKind;
x_36 = l_Lean_Parser_ParserState_mkNode(x_6, x_35, x_14);
return x_36;
}
}
}
}
lean_object* l_Lean_Parser_many1Indent(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_Parser_inhabited___closed__1;
x_6 = l_Lean_Parser_andthenInfo(x_5, x_4);
x_7 = lean_box(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent___lambda__1___boxed), 6, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__1(x_9, x_2, x_3, x_4, x_10, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Parser_manyAux___main___at_Lean_Parser_many1Indent___spec__2(x_9, x_2, x_3, x_4, x_10, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Parser_many1Indent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_many1Indent___lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_many1Indent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_many1Indent(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
else
{
lean_object* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_19, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_16, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_31, x_2, x_3);
lean_ctor_set(x_1, 3, x_35);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_31, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = 0;
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
x_60 = 1;
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_60);
lean_ctor_set(x_36, 3, x_59);
lean_ctor_set(x_36, 2, x_58);
lean_ctor_set(x_36, 1, x_57);
lean_ctor_set(x_36, 0, x_56);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_60);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
lean_ctor_set(x_36, 3, x_64);
lean_ctor_set(x_36, 2, x_63);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_61);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_65);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = 1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 4, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_28);
lean_ctor_set(x_75, 1, x_29);
lean_ctor_set(x_75, 2, x_30);
lean_ctor_set(x_75, 3, x_37);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_36, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_36, 0);
lean_dec(x_79);
x_80 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_36, 1);
x_82 = lean_ctor_get(x_36, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_38);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
x_91 = lean_ctor_get(x_37, 2);
x_92 = lean_ctor_get(x_37, 3);
x_93 = 1;
lean_ctor_set(x_37, 3, x_89);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_93);
lean_ctor_set(x_36, 0, x_92);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
x_96 = lean_ctor_get(x_37, 2);
x_97 = lean_ctor_get(x_37, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
x_98 = 1;
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_29);
lean_ctor_set(x_99, 2, x_30);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_98);
lean_ctor_set(x_36, 0, x_97);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_98);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_96);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_36, 1);
x_101 = lean_ctor_get(x_36, 2);
x_102 = lean_ctor_get(x_36, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_103 = lean_ctor_get(x_37, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_107 = x_37;
} else {
 lean_dec_ref(x_37);
 x_107 = lean_box(0);
}
x_108 = 1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_28);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_30);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_110);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_36, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_36, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_36, 0);
lean_dec(x_114);
x_115 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_36, 1);
x_117 = lean_ctor_get(x_36, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = 0;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_1);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_36, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_111);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
x_127 = lean_ctor_get(x_111, 2);
x_128 = lean_ctor_get(x_111, 3);
lean_inc(x_37);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set(x_111, 2, x_30);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_28);
x_129 = !lean_is_exclusive(x_37);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_37, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_37, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_37, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
lean_ctor_set(x_37, 3, x_128);
lean_ctor_set(x_37, 2, x_127);
lean_ctor_set(x_37, 1, x_126);
lean_ctor_set(x_37, 0, x_125);
lean_ctor_set(x_36, 3, x_37);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
lean_object* x_134; 
lean_dec(x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_134);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_111, 0);
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_111);
lean_inc(x_37);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_140 = x_37;
} else {
 lean_dec_ref(x_37);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_141);
lean_ctor_set(x_36, 0, x_139);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_36, 1);
x_143 = lean_ctor_get(x_36, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_ctor_get(x_111, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_111, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_111, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_111, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_148 = x_111;
} else {
 lean_dec_ref(x_111);
 x_148 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_29);
lean_ctor_set(x_149, 2, x_30);
lean_ctor_set(x_149, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_150 = x_37;
} else {
 lean_dec_ref(x_37);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_142);
lean_ctor_set(x_152, 2, x_143);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_36);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_36, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_36, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_37, 0);
x_159 = lean_ctor_get(x_37, 1);
x_160 = lean_ctor_get(x_37, 2);
x_161 = lean_ctor_get(x_37, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_37);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean_ctor_set(x_36, 0, x_162);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_163);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_36, 1);
x_165 = lean_ctor_get(x_36, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_36);
x_166 = lean_ctor_get(x_37, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_37, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_37, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_37, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_170 = x_37;
} else {
 lean_dec_ref(x_37);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
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
uint8_t x_174; 
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_28, x_2, x_3);
lean_ctor_set(x_1, 0, x_175);
return x_1;
}
else
{
lean_object* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_28, x_2, x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_free_object(x_1);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 3);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_176, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_176, 0);
lean_dec(x_181);
x_182 = 0;
lean_ctor_set(x_176, 0, x_178);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_176, 1);
x_185 = lean_ctor_get(x_176, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = 0;
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8_t x_189; 
x_189 = lean_ctor_get_uint8(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_176, 1);
x_192 = lean_ctor_get(x_176, 2);
x_193 = lean_ctor_get(x_176, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_176, 0);
lean_dec(x_194);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 2);
x_199 = lean_ctor_get(x_178, 3);
x_200 = 1;
lean_ctor_set(x_178, 3, x_196);
lean_ctor_set(x_178, 2, x_192);
lean_ctor_set(x_178, 1, x_191);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_200);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_199);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_200);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_198);
lean_ctor_set(x_1, 1, x_197);
lean_ctor_set(x_1, 0, x_178);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_178, 0);
x_202 = lean_ctor_get(x_178, 1);
x_203 = lean_ctor_get(x_178, 2);
x_204 = lean_ctor_get(x_178, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_178);
x_205 = 1;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_177);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_204);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_205);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_203);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_176, 1);
x_208 = lean_ctor_get(x_176, 2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_176);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_178, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_178, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 x_213 = x_178;
} else {
 lean_dec_ref(x_178);
 x_213 = lean_box(0);
}
x_214 = 1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_177);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_208);
lean_ctor_set(x_215, 3, x_209);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_29);
lean_ctor_set(x_216, 2, x_30);
lean_ctor_set(x_216, 3, x_31);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_214);
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_176);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 0);
lean_dec(x_219);
x_220 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_220);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_176, 1);
x_222 = lean_ctor_get(x_176, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_177);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_176, 1);
x_228 = lean_ctor_get(x_176, 2);
x_229 = lean_ctor_get(x_176, 3);
x_230 = lean_ctor_get(x_176, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_177);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = 1;
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_232);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_177);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_177, 0);
x_234 = lean_ctor_get(x_177, 1);
x_235 = lean_ctor_get(x_177, 2);
x_236 = lean_ctor_get(x_177, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_177);
x_237 = 1;
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_237);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_237);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_176, 1);
x_240 = lean_ctor_get(x_176, 2);
x_241 = lean_ctor_get(x_176, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_242 = lean_ctor_get(x_177, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_177, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_177, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_177, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_246 = x_177;
} else {
 lean_dec_ref(x_177);
 x_246 = lean_box(0);
}
x_247 = 1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
lean_ctor_set(x_248, 2, x_244);
lean_ctor_set(x_248, 3, x_245);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_29);
lean_ctor_set(x_249, 2, x_30);
lean_ctor_set(x_249, 3, x_31);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_249);
lean_ctor_set(x_1, 2, x_240);
lean_ctor_set(x_1, 1, x_239);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_176, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_176, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_176, 0);
lean_dec(x_253);
x_254 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_254);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_176, 1);
x_256 = lean_ctor_get(x_176, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_176);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_177);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8_t x_260; 
lean_free_object(x_1);
x_260 = !lean_is_exclusive(x_176);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_261 = lean_ctor_get(x_176, 1);
x_262 = lean_ctor_get(x_176, 2);
x_263 = lean_ctor_get(x_176, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_176, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
x_268 = lean_ctor_get(x_250, 2);
x_269 = lean_ctor_get(x_250, 3);
lean_inc(x_177);
lean_ctor_set(x_250, 3, x_266);
lean_ctor_set(x_250, 2, x_262);
lean_ctor_set(x_250, 1, x_261);
lean_ctor_set(x_250, 0, x_177);
x_270 = !lean_is_exclusive(x_177);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_177, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_177, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_177, 0);
lean_dec(x_274);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
lean_ctor_set(x_177, 3, x_31);
lean_ctor_set(x_177, 2, x_30);
lean_ctor_set(x_177, 1, x_29);
lean_ctor_set(x_177, 0, x_269);
lean_ctor_set(x_176, 3, x_177);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
lean_object* x_275; 
lean_dec(x_177);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_29);
lean_ctor_set(x_275, 2, x_30);
lean_ctor_set(x_275, 3, x_31);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_275);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
x_278 = lean_ctor_get(x_250, 2);
x_279 = lean_ctor_get(x_250, 3);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
lean_inc(x_177);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_177);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_262);
lean_ctor_set(x_280, 3, x_276);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_281 = x_177;
} else {
 lean_dec_ref(x_177);
 x_281 = lean_box(0);
}
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 4, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_29);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_31);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_282);
lean_ctor_set(x_176, 2, x_278);
lean_ctor_set(x_176, 1, x_277);
lean_ctor_set(x_176, 0, x_280);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_176, 1);
x_284 = lean_ctor_get(x_176, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_176);
x_285 = lean_ctor_get(x_250, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_250, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
lean_inc(x_177);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_177);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_285);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_291 = x_177;
} else {
 lean_dec_ref(x_177);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_29);
lean_ctor_set(x_292, 2, x_30);
lean_ctor_set(x_292, 3, x_31);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_176);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_176, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_176, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_177);
if (x_297 == 0)
{
uint8_t x_298; 
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_177, 0);
x_300 = lean_ctor_get(x_177, 1);
x_301 = lean_ctor_get(x_177, 2);
x_302 = lean_ctor_get(x_177, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_177);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean_ctor_set(x_176, 0, x_303);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_304);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_305 = lean_ctor_get(x_176, 1);
x_306 = lean_ctor_get(x_176, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_176);
x_307 = lean_ctor_get(x_177, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_177, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_177, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_177, 3);
lean_inc(x_310);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_311 = x_177;
} else {
 lean_dec_ref(x_177);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_306);
lean_ctor_set(x_314, 3, x_250);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
lean_ctor_set(x_1, 0, x_314);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_ctor_get(x_1, 2);
x_318 = lean_ctor_get(x_1, 3);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_317);
lean_dec(x_316);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_2);
lean_ctor_set(x_321, 2, x_3);
lean_ctor_set(x_321, 3, x_318);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_318, x_2, x_3);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_317);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
lean_object* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_318, x_2, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
return x_325;
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 2);
lean_inc(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_328);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_316);
lean_ctor_set(x_334, 2, x_317);
lean_ctor_set(x_334, 3, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_327, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
x_344 = 1;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_315);
lean_ctor_set(x_345, 1, x_316);
lean_ctor_set(x_345, 2, x_317);
lean_ctor_set(x_345, 3, x_326);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_338)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_338;
}
lean_ctor_set(x_346, 0, x_339);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_341);
lean_ctor_set(x_346, 3, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_337);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_325, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 2);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
x_351 = 0;
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(1, 4, 1);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_326);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_353, 0, x_315);
lean_ctor_set(x_353, 1, x_316);
lean_ctor_set(x_353, 2, x_317);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_358 = x_325;
} else {
 lean_dec_ref(x_325);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_326, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_326, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_326, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_363 = x_326;
} else {
 lean_dec_ref(x_326);
 x_363 = lean_box(0);
}
x_364 = 1;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_315);
lean_ctor_set(x_365, 1, x_316);
lean_ctor_set(x_365, 2, x_317);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_358;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set(x_366, 3, x_357);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_361);
lean_ctor_set(x_367, 3, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_325, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_325, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_325, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_371 = x_325;
} else {
 lean_dec_ref(x_325);
 x_371 = lean_box(0);
}
x_372 = 0;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_326);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_370);
lean_ctor_set(x_373, 3, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_316);
lean_ctor_set(x_374, 2, x_317);
lean_ctor_set(x_374, 3, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_325, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_325, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_378 = x_325;
} else {
 lean_dec_ref(x_325);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_368, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
lean_inc(x_326);
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_315);
lean_ctor_set(x_384, 1, x_316);
lean_ctor_set(x_384, 2, x_317);
lean_ctor_set(x_384, 3, x_326);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_385 = x_326;
} else {
 lean_dec_ref(x_326);
 x_385 = lean_box(0);
}
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_378)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_378;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_376);
lean_ctor_set(x_387, 2, x_377);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; 
x_388 = lean_ctor_get(x_325, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_325, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_390 = x_325;
} else {
 lean_dec_ref(x_325);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_326, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_326, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_326, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_326, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_395 = x_326;
} else {
 lean_dec_ref(x_326);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_391);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_393);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_388);
lean_ctor_set(x_398, 2, x_389);
lean_ctor_set(x_398, 3, x_368);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_315);
lean_ctor_set(x_399, 1, x_316);
lean_ctor_set(x_399, 2, x_317);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_375);
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
uint8_t x_400; 
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_315, x_2, x_3);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_316);
lean_ctor_set(x_402, 2, x_317);
lean_ctor_set(x_402, 3, x_318);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
lean_object* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_315, x_2, x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
return x_403;
}
else
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = 0;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set(x_410, 2, x_407);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_316);
lean_ctor_set(x_412, 2, x_317);
lean_ctor_set(x_412, 3, x_318);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8_t x_413; 
x_413 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_403, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_405, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 2);
lean_inc(x_419);
x_420 = lean_ctor_get(x_405, 3);
lean_inc(x_420);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_421 = x_405;
} else {
 lean_dec_ref(x_405);
 x_421 = lean_box(0);
}
x_422 = 1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_417);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean_is_scalar(x_416)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_416;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_316);
lean_ctor_set(x_424, 2, x_317);
lean_ctor_set(x_424, 3, x_318);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_418);
lean_ctor_set(x_425, 2, x_419);
lean_ctor_set(x_425, 3, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_403, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_403, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_428 = x_403;
} else {
 lean_dec_ref(x_403);
 x_428 = lean_box(0);
}
x_429 = 0;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_404);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_427);
lean_ctor_set(x_430, 3, x_405);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_316);
lean_ctor_set(x_431, 2, x_317);
lean_ctor_set(x_431, 3, x_318);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_403, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_403, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_403, 3);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_404, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_404, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_404, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_404, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_441 = x_404;
} else {
 lean_dec_ref(x_404);
 x_441 = lean_box(0);
}
x_442 = 1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set(x_443, 2, x_439);
lean_ctor_set(x_443, 3, x_440);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_436;
}
lean_ctor_set(x_444, 0, x_435);
lean_ctor_set(x_444, 1, x_316);
lean_ctor_set(x_444, 2, x_317);
lean_ctor_set(x_444, 3, x_318);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_403, 3);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_403, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_403, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_449 = x_403;
} else {
 lean_dec_ref(x_403);
 x_449 = lean_box(0);
}
x_450 = 0;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_447);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_316);
lean_ctor_set(x_452, 2, x_317);
lean_ctor_set(x_452, 3, x_318);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = lean_ctor_get_uint8(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_403, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_456 = x_403;
} else {
 lean_dec_ref(x_403);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_461 = x_446;
} else {
 lean_dec_ref(x_446);
 x_461 = lean_box(0);
}
lean_inc(x_404);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_457);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_463 = x_404;
} else {
 lean_dec_ref(x_404);
 x_463 = lean_box(0);
}
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_316);
lean_ctor_set(x_464, 2, x_317);
lean_ctor_set(x_464, 3, x_318);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 4, 1);
} else {
 x_465 = x_456;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_459);
lean_ctor_set(x_465, 3, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_403, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_403, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_468 = x_403;
} else {
 lean_dec_ref(x_403);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_404, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_404, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_404, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_473 = x_404;
} else {
 lean_dec_ref(x_404);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_469);
lean_ctor_set(x_474, 1, x_470);
lean_ctor_set(x_474, 2, x_471);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean_is_scalar(x_468)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_468;
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_466);
lean_ctor_set(x_476, 2, x_467);
lean_ctor_set(x_476, 3, x_446);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_316);
lean_ctor_set(x_477, 2, x_317);
lean_ctor_set(x_477, 3, x_318);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_453);
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
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
else
{
lean_object* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_19, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_16, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_31, x_2, x_3);
lean_ctor_set(x_1, 3, x_35);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_31, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = 0;
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
x_60 = 1;
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_60);
lean_ctor_set(x_36, 3, x_59);
lean_ctor_set(x_36, 2, x_58);
lean_ctor_set(x_36, 1, x_57);
lean_ctor_set(x_36, 0, x_56);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_60);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
lean_ctor_set(x_36, 3, x_64);
lean_ctor_set(x_36, 2, x_63);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_61);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_65);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = 1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 4, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_28);
lean_ctor_set(x_75, 1, x_29);
lean_ctor_set(x_75, 2, x_30);
lean_ctor_set(x_75, 3, x_37);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_36, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_36, 0);
lean_dec(x_79);
x_80 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_36, 1);
x_82 = lean_ctor_get(x_36, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_38);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
x_91 = lean_ctor_get(x_37, 2);
x_92 = lean_ctor_get(x_37, 3);
x_93 = 1;
lean_ctor_set(x_37, 3, x_89);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_93);
lean_ctor_set(x_36, 0, x_92);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
x_96 = lean_ctor_get(x_37, 2);
x_97 = lean_ctor_get(x_37, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
x_98 = 1;
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_29);
lean_ctor_set(x_99, 2, x_30);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_98);
lean_ctor_set(x_36, 0, x_97);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_98);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_96);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_36, 1);
x_101 = lean_ctor_get(x_36, 2);
x_102 = lean_ctor_get(x_36, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_103 = lean_ctor_get(x_37, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_107 = x_37;
} else {
 lean_dec_ref(x_37);
 x_107 = lean_box(0);
}
x_108 = 1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_28);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_30);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_110);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_36, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_36, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_36, 0);
lean_dec(x_114);
x_115 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_36, 1);
x_117 = lean_ctor_get(x_36, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = 0;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_1);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_36, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_111);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
x_127 = lean_ctor_get(x_111, 2);
x_128 = lean_ctor_get(x_111, 3);
lean_inc(x_37);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set(x_111, 2, x_30);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_28);
x_129 = !lean_is_exclusive(x_37);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_37, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_37, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_37, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
lean_ctor_set(x_37, 3, x_128);
lean_ctor_set(x_37, 2, x_127);
lean_ctor_set(x_37, 1, x_126);
lean_ctor_set(x_37, 0, x_125);
lean_ctor_set(x_36, 3, x_37);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
lean_object* x_134; 
lean_dec(x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_134);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_111, 0);
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_111);
lean_inc(x_37);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_140 = x_37;
} else {
 lean_dec_ref(x_37);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_141);
lean_ctor_set(x_36, 0, x_139);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_36, 1);
x_143 = lean_ctor_get(x_36, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_ctor_get(x_111, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_111, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_111, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_111, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_148 = x_111;
} else {
 lean_dec_ref(x_111);
 x_148 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_29);
lean_ctor_set(x_149, 2, x_30);
lean_ctor_set(x_149, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_150 = x_37;
} else {
 lean_dec_ref(x_37);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_142);
lean_ctor_set(x_152, 2, x_143);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_36);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_36, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_36, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_37, 0);
x_159 = lean_ctor_get(x_37, 1);
x_160 = lean_ctor_get(x_37, 2);
x_161 = lean_ctor_get(x_37, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_37);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean_ctor_set(x_36, 0, x_162);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_163);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_36, 1);
x_165 = lean_ctor_get(x_36, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_36);
x_166 = lean_ctor_get(x_37, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_37, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_37, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_37, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_170 = x_37;
} else {
 lean_dec_ref(x_37);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
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
uint8_t x_174; 
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_28, x_2, x_3);
lean_ctor_set(x_1, 0, x_175);
return x_1;
}
else
{
lean_object* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_28, x_2, x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_free_object(x_1);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 3);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_176, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_176, 0);
lean_dec(x_181);
x_182 = 0;
lean_ctor_set(x_176, 0, x_178);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_176, 1);
x_185 = lean_ctor_get(x_176, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = 0;
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8_t x_189; 
x_189 = lean_ctor_get_uint8(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_176, 1);
x_192 = lean_ctor_get(x_176, 2);
x_193 = lean_ctor_get(x_176, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_176, 0);
lean_dec(x_194);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 2);
x_199 = lean_ctor_get(x_178, 3);
x_200 = 1;
lean_ctor_set(x_178, 3, x_196);
lean_ctor_set(x_178, 2, x_192);
lean_ctor_set(x_178, 1, x_191);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_200);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_199);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_200);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_198);
lean_ctor_set(x_1, 1, x_197);
lean_ctor_set(x_1, 0, x_178);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_178, 0);
x_202 = lean_ctor_get(x_178, 1);
x_203 = lean_ctor_get(x_178, 2);
x_204 = lean_ctor_get(x_178, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_178);
x_205 = 1;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_177);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_204);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_205);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_203);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_176, 1);
x_208 = lean_ctor_get(x_176, 2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_176);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_178, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_178, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 x_213 = x_178;
} else {
 lean_dec_ref(x_178);
 x_213 = lean_box(0);
}
x_214 = 1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_177);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_208);
lean_ctor_set(x_215, 3, x_209);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_29);
lean_ctor_set(x_216, 2, x_30);
lean_ctor_set(x_216, 3, x_31);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_214);
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_176);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 0);
lean_dec(x_219);
x_220 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_220);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_176, 1);
x_222 = lean_ctor_get(x_176, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_177);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_176, 1);
x_228 = lean_ctor_get(x_176, 2);
x_229 = lean_ctor_get(x_176, 3);
x_230 = lean_ctor_get(x_176, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_177);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = 1;
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_232);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_177);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_177, 0);
x_234 = lean_ctor_get(x_177, 1);
x_235 = lean_ctor_get(x_177, 2);
x_236 = lean_ctor_get(x_177, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_177);
x_237 = 1;
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_237);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_237);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_176, 1);
x_240 = lean_ctor_get(x_176, 2);
x_241 = lean_ctor_get(x_176, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_242 = lean_ctor_get(x_177, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_177, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_177, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_177, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_246 = x_177;
} else {
 lean_dec_ref(x_177);
 x_246 = lean_box(0);
}
x_247 = 1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
lean_ctor_set(x_248, 2, x_244);
lean_ctor_set(x_248, 3, x_245);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_29);
lean_ctor_set(x_249, 2, x_30);
lean_ctor_set(x_249, 3, x_31);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_249);
lean_ctor_set(x_1, 2, x_240);
lean_ctor_set(x_1, 1, x_239);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_176, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_176, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_176, 0);
lean_dec(x_253);
x_254 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_254);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_176, 1);
x_256 = lean_ctor_get(x_176, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_176);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_177);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8_t x_260; 
lean_free_object(x_1);
x_260 = !lean_is_exclusive(x_176);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_261 = lean_ctor_get(x_176, 1);
x_262 = lean_ctor_get(x_176, 2);
x_263 = lean_ctor_get(x_176, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_176, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
x_268 = lean_ctor_get(x_250, 2);
x_269 = lean_ctor_get(x_250, 3);
lean_inc(x_177);
lean_ctor_set(x_250, 3, x_266);
lean_ctor_set(x_250, 2, x_262);
lean_ctor_set(x_250, 1, x_261);
lean_ctor_set(x_250, 0, x_177);
x_270 = !lean_is_exclusive(x_177);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_177, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_177, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_177, 0);
lean_dec(x_274);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
lean_ctor_set(x_177, 3, x_31);
lean_ctor_set(x_177, 2, x_30);
lean_ctor_set(x_177, 1, x_29);
lean_ctor_set(x_177, 0, x_269);
lean_ctor_set(x_176, 3, x_177);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
lean_object* x_275; 
lean_dec(x_177);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_29);
lean_ctor_set(x_275, 2, x_30);
lean_ctor_set(x_275, 3, x_31);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_275);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
x_278 = lean_ctor_get(x_250, 2);
x_279 = lean_ctor_get(x_250, 3);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
lean_inc(x_177);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_177);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_262);
lean_ctor_set(x_280, 3, x_276);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_281 = x_177;
} else {
 lean_dec_ref(x_177);
 x_281 = lean_box(0);
}
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 4, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_29);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_31);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_282);
lean_ctor_set(x_176, 2, x_278);
lean_ctor_set(x_176, 1, x_277);
lean_ctor_set(x_176, 0, x_280);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_176, 1);
x_284 = lean_ctor_get(x_176, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_176);
x_285 = lean_ctor_get(x_250, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_250, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
lean_inc(x_177);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_177);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_285);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_291 = x_177;
} else {
 lean_dec_ref(x_177);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_29);
lean_ctor_set(x_292, 2, x_30);
lean_ctor_set(x_292, 3, x_31);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_176);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_176, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_176, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_177);
if (x_297 == 0)
{
uint8_t x_298; 
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_177, 0);
x_300 = lean_ctor_get(x_177, 1);
x_301 = lean_ctor_get(x_177, 2);
x_302 = lean_ctor_get(x_177, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_177);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean_ctor_set(x_176, 0, x_303);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_304);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_305 = lean_ctor_get(x_176, 1);
x_306 = lean_ctor_get(x_176, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_176);
x_307 = lean_ctor_get(x_177, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_177, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_177, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_177, 3);
lean_inc(x_310);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_311 = x_177;
} else {
 lean_dec_ref(x_177);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_306);
lean_ctor_set(x_314, 3, x_250);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
lean_ctor_set(x_1, 0, x_314);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_ctor_get(x_1, 2);
x_318 = lean_ctor_get(x_1, 3);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_317);
lean_dec(x_316);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_2);
lean_ctor_set(x_321, 2, x_3);
lean_ctor_set(x_321, 3, x_318);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_318, x_2, x_3);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_317);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
lean_object* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_318, x_2, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
return x_325;
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 2);
lean_inc(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_328);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_316);
lean_ctor_set(x_334, 2, x_317);
lean_ctor_set(x_334, 3, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_327, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
x_344 = 1;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_315);
lean_ctor_set(x_345, 1, x_316);
lean_ctor_set(x_345, 2, x_317);
lean_ctor_set(x_345, 3, x_326);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_338)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_338;
}
lean_ctor_set(x_346, 0, x_339);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_341);
lean_ctor_set(x_346, 3, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_337);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_325, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 2);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
x_351 = 0;
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(1, 4, 1);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_326);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_353, 0, x_315);
lean_ctor_set(x_353, 1, x_316);
lean_ctor_set(x_353, 2, x_317);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_358 = x_325;
} else {
 lean_dec_ref(x_325);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_326, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_326, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_326, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_363 = x_326;
} else {
 lean_dec_ref(x_326);
 x_363 = lean_box(0);
}
x_364 = 1;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_315);
lean_ctor_set(x_365, 1, x_316);
lean_ctor_set(x_365, 2, x_317);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_358;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set(x_366, 3, x_357);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_361);
lean_ctor_set(x_367, 3, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_325, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_325, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_325, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_371 = x_325;
} else {
 lean_dec_ref(x_325);
 x_371 = lean_box(0);
}
x_372 = 0;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_326);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_370);
lean_ctor_set(x_373, 3, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_316);
lean_ctor_set(x_374, 2, x_317);
lean_ctor_set(x_374, 3, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_325, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_325, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_378 = x_325;
} else {
 lean_dec_ref(x_325);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_368, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
lean_inc(x_326);
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_315);
lean_ctor_set(x_384, 1, x_316);
lean_ctor_set(x_384, 2, x_317);
lean_ctor_set(x_384, 3, x_326);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_385 = x_326;
} else {
 lean_dec_ref(x_326);
 x_385 = lean_box(0);
}
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_378)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_378;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_376);
lean_ctor_set(x_387, 2, x_377);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; 
x_388 = lean_ctor_get(x_325, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_325, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_390 = x_325;
} else {
 lean_dec_ref(x_325);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_326, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_326, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_326, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_326, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_395 = x_326;
} else {
 lean_dec_ref(x_326);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_391);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_393);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_388);
lean_ctor_set(x_398, 2, x_389);
lean_ctor_set(x_398, 3, x_368);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_315);
lean_ctor_set(x_399, 1, x_316);
lean_ctor_set(x_399, 2, x_317);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_375);
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
uint8_t x_400; 
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_315, x_2, x_3);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_316);
lean_ctor_set(x_402, 2, x_317);
lean_ctor_set(x_402, 3, x_318);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
lean_object* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_315, x_2, x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
return x_403;
}
else
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = 0;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set(x_410, 2, x_407);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_316);
lean_ctor_set(x_412, 2, x_317);
lean_ctor_set(x_412, 3, x_318);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8_t x_413; 
x_413 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_403, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_405, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 2);
lean_inc(x_419);
x_420 = lean_ctor_get(x_405, 3);
lean_inc(x_420);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_421 = x_405;
} else {
 lean_dec_ref(x_405);
 x_421 = lean_box(0);
}
x_422 = 1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_417);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean_is_scalar(x_416)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_416;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_316);
lean_ctor_set(x_424, 2, x_317);
lean_ctor_set(x_424, 3, x_318);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_418);
lean_ctor_set(x_425, 2, x_419);
lean_ctor_set(x_425, 3, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_403, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_403, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_428 = x_403;
} else {
 lean_dec_ref(x_403);
 x_428 = lean_box(0);
}
x_429 = 0;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_404);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_427);
lean_ctor_set(x_430, 3, x_405);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_316);
lean_ctor_set(x_431, 2, x_317);
lean_ctor_set(x_431, 3, x_318);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_403, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_403, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_403, 3);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_404, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_404, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_404, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_404, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_441 = x_404;
} else {
 lean_dec_ref(x_404);
 x_441 = lean_box(0);
}
x_442 = 1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set(x_443, 2, x_439);
lean_ctor_set(x_443, 3, x_440);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_436;
}
lean_ctor_set(x_444, 0, x_435);
lean_ctor_set(x_444, 1, x_316);
lean_ctor_set(x_444, 2, x_317);
lean_ctor_set(x_444, 3, x_318);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_403, 3);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_403, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_403, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_449 = x_403;
} else {
 lean_dec_ref(x_403);
 x_449 = lean_box(0);
}
x_450 = 0;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_447);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_316);
lean_ctor_set(x_452, 2, x_317);
lean_ctor_set(x_452, 3, x_318);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = lean_ctor_get_uint8(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_403, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_456 = x_403;
} else {
 lean_dec_ref(x_403);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_461 = x_446;
} else {
 lean_dec_ref(x_446);
 x_461 = lean_box(0);
}
lean_inc(x_404);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_457);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_463 = x_404;
} else {
 lean_dec_ref(x_404);
 x_463 = lean_box(0);
}
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_316);
lean_ctor_set(x_464, 2, x_317);
lean_ctor_set(x_464, 3, x_318);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 4, 1);
} else {
 x_465 = x_456;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_459);
lean_ctor_set(x_465, 3, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_403, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_403, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_468 = x_403;
} else {
 lean_dec_ref(x_403);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_404, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_404, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_404, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_473 = x_404;
} else {
 lean_dec_ref(x_404);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_469);
lean_ctor_set(x_474, 1, x_470);
lean_ctor_set(x_474, 2, x_471);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean_is_scalar(x_468)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_468;
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_466);
lean_ctor_set(x_476, 2, x_467);
lean_ctor_set(x_476, 3, x_446);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_316);
lean_ctor_set(x_477, 2, x_317);
lean_ctor_set(x_477, 3, x_318);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_453);
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
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
else
{
lean_object* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_19, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_16, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_31, x_2, x_3);
lean_ctor_set(x_1, 3, x_35);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_31, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = 0;
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
x_60 = 1;
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_60);
lean_ctor_set(x_36, 3, x_59);
lean_ctor_set(x_36, 2, x_58);
lean_ctor_set(x_36, 1, x_57);
lean_ctor_set(x_36, 0, x_56);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_60);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
lean_ctor_set(x_36, 3, x_64);
lean_ctor_set(x_36, 2, x_63);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_61);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_65);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = 1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 4, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_28);
lean_ctor_set(x_75, 1, x_29);
lean_ctor_set(x_75, 2, x_30);
lean_ctor_set(x_75, 3, x_37);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_36, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_36, 0);
lean_dec(x_79);
x_80 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_36, 1);
x_82 = lean_ctor_get(x_36, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_38);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
x_91 = lean_ctor_get(x_37, 2);
x_92 = lean_ctor_get(x_37, 3);
x_93 = 1;
lean_ctor_set(x_37, 3, x_89);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_93);
lean_ctor_set(x_36, 0, x_92);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
x_96 = lean_ctor_get(x_37, 2);
x_97 = lean_ctor_get(x_37, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
x_98 = 1;
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_29);
lean_ctor_set(x_99, 2, x_30);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_98);
lean_ctor_set(x_36, 0, x_97);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_98);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_96);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_36, 1);
x_101 = lean_ctor_get(x_36, 2);
x_102 = lean_ctor_get(x_36, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_103 = lean_ctor_get(x_37, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_107 = x_37;
} else {
 lean_dec_ref(x_37);
 x_107 = lean_box(0);
}
x_108 = 1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_28);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_30);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_110);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_36, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_36, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_36, 0);
lean_dec(x_114);
x_115 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_36, 1);
x_117 = lean_ctor_get(x_36, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = 0;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_1);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_36, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_111);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
x_127 = lean_ctor_get(x_111, 2);
x_128 = lean_ctor_get(x_111, 3);
lean_inc(x_37);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set(x_111, 2, x_30);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_28);
x_129 = !lean_is_exclusive(x_37);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_37, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_37, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_37, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
lean_ctor_set(x_37, 3, x_128);
lean_ctor_set(x_37, 2, x_127);
lean_ctor_set(x_37, 1, x_126);
lean_ctor_set(x_37, 0, x_125);
lean_ctor_set(x_36, 3, x_37);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
lean_object* x_134; 
lean_dec(x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_134);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_111, 0);
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_111);
lean_inc(x_37);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_140 = x_37;
} else {
 lean_dec_ref(x_37);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_141);
lean_ctor_set(x_36, 0, x_139);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_36, 1);
x_143 = lean_ctor_get(x_36, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_ctor_get(x_111, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_111, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_111, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_111, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_148 = x_111;
} else {
 lean_dec_ref(x_111);
 x_148 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_29);
lean_ctor_set(x_149, 2, x_30);
lean_ctor_set(x_149, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_150 = x_37;
} else {
 lean_dec_ref(x_37);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_142);
lean_ctor_set(x_152, 2, x_143);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_36);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_36, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_36, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_37, 0);
x_159 = lean_ctor_get(x_37, 1);
x_160 = lean_ctor_get(x_37, 2);
x_161 = lean_ctor_get(x_37, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_37);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean_ctor_set(x_36, 0, x_162);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_163);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_36, 1);
x_165 = lean_ctor_get(x_36, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_36);
x_166 = lean_ctor_get(x_37, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_37, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_37, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_37, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_170 = x_37;
} else {
 lean_dec_ref(x_37);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
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
uint8_t x_174; 
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_28, x_2, x_3);
lean_ctor_set(x_1, 0, x_175);
return x_1;
}
else
{
lean_object* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_28, x_2, x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_free_object(x_1);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 3);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_176, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_176, 0);
lean_dec(x_181);
x_182 = 0;
lean_ctor_set(x_176, 0, x_178);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_176, 1);
x_185 = lean_ctor_get(x_176, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = 0;
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8_t x_189; 
x_189 = lean_ctor_get_uint8(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_176, 1);
x_192 = lean_ctor_get(x_176, 2);
x_193 = lean_ctor_get(x_176, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_176, 0);
lean_dec(x_194);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 2);
x_199 = lean_ctor_get(x_178, 3);
x_200 = 1;
lean_ctor_set(x_178, 3, x_196);
lean_ctor_set(x_178, 2, x_192);
lean_ctor_set(x_178, 1, x_191);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_200);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_199);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_200);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_198);
lean_ctor_set(x_1, 1, x_197);
lean_ctor_set(x_1, 0, x_178);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_178, 0);
x_202 = lean_ctor_get(x_178, 1);
x_203 = lean_ctor_get(x_178, 2);
x_204 = lean_ctor_get(x_178, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_178);
x_205 = 1;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_177);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_204);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_205);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_203);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_176, 1);
x_208 = lean_ctor_get(x_176, 2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_176);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_178, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_178, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 x_213 = x_178;
} else {
 lean_dec_ref(x_178);
 x_213 = lean_box(0);
}
x_214 = 1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_177);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_208);
lean_ctor_set(x_215, 3, x_209);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_29);
lean_ctor_set(x_216, 2, x_30);
lean_ctor_set(x_216, 3, x_31);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_214);
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_176);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 0);
lean_dec(x_219);
x_220 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_220);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_176, 1);
x_222 = lean_ctor_get(x_176, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_177);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_176, 1);
x_228 = lean_ctor_get(x_176, 2);
x_229 = lean_ctor_get(x_176, 3);
x_230 = lean_ctor_get(x_176, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_177);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = 1;
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_232);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_177);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_177, 0);
x_234 = lean_ctor_get(x_177, 1);
x_235 = lean_ctor_get(x_177, 2);
x_236 = lean_ctor_get(x_177, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_177);
x_237 = 1;
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_237);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_237);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_176, 1);
x_240 = lean_ctor_get(x_176, 2);
x_241 = lean_ctor_get(x_176, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_242 = lean_ctor_get(x_177, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_177, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_177, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_177, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_246 = x_177;
} else {
 lean_dec_ref(x_177);
 x_246 = lean_box(0);
}
x_247 = 1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
lean_ctor_set(x_248, 2, x_244);
lean_ctor_set(x_248, 3, x_245);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_29);
lean_ctor_set(x_249, 2, x_30);
lean_ctor_set(x_249, 3, x_31);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_249);
lean_ctor_set(x_1, 2, x_240);
lean_ctor_set(x_1, 1, x_239);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_176, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_176, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_176, 0);
lean_dec(x_253);
x_254 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_254);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_176, 1);
x_256 = lean_ctor_get(x_176, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_176);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_177);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8_t x_260; 
lean_free_object(x_1);
x_260 = !lean_is_exclusive(x_176);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_261 = lean_ctor_get(x_176, 1);
x_262 = lean_ctor_get(x_176, 2);
x_263 = lean_ctor_get(x_176, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_176, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
x_268 = lean_ctor_get(x_250, 2);
x_269 = lean_ctor_get(x_250, 3);
lean_inc(x_177);
lean_ctor_set(x_250, 3, x_266);
lean_ctor_set(x_250, 2, x_262);
lean_ctor_set(x_250, 1, x_261);
lean_ctor_set(x_250, 0, x_177);
x_270 = !lean_is_exclusive(x_177);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_177, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_177, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_177, 0);
lean_dec(x_274);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
lean_ctor_set(x_177, 3, x_31);
lean_ctor_set(x_177, 2, x_30);
lean_ctor_set(x_177, 1, x_29);
lean_ctor_set(x_177, 0, x_269);
lean_ctor_set(x_176, 3, x_177);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
lean_object* x_275; 
lean_dec(x_177);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_29);
lean_ctor_set(x_275, 2, x_30);
lean_ctor_set(x_275, 3, x_31);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_275);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
x_278 = lean_ctor_get(x_250, 2);
x_279 = lean_ctor_get(x_250, 3);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
lean_inc(x_177);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_177);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_262);
lean_ctor_set(x_280, 3, x_276);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_281 = x_177;
} else {
 lean_dec_ref(x_177);
 x_281 = lean_box(0);
}
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 4, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_29);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_31);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_282);
lean_ctor_set(x_176, 2, x_278);
lean_ctor_set(x_176, 1, x_277);
lean_ctor_set(x_176, 0, x_280);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_176, 1);
x_284 = lean_ctor_get(x_176, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_176);
x_285 = lean_ctor_get(x_250, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_250, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
lean_inc(x_177);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_177);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_285);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_291 = x_177;
} else {
 lean_dec_ref(x_177);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_29);
lean_ctor_set(x_292, 2, x_30);
lean_ctor_set(x_292, 3, x_31);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_176);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_176, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_176, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_177);
if (x_297 == 0)
{
uint8_t x_298; 
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_177, 0);
x_300 = lean_ctor_get(x_177, 1);
x_301 = lean_ctor_get(x_177, 2);
x_302 = lean_ctor_get(x_177, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_177);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean_ctor_set(x_176, 0, x_303);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_304);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_305 = lean_ctor_get(x_176, 1);
x_306 = lean_ctor_get(x_176, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_176);
x_307 = lean_ctor_get(x_177, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_177, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_177, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_177, 3);
lean_inc(x_310);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_311 = x_177;
} else {
 lean_dec_ref(x_177);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_306);
lean_ctor_set(x_314, 3, x_250);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
lean_ctor_set(x_1, 0, x_314);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_ctor_get(x_1, 2);
x_318 = lean_ctor_get(x_1, 3);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_317);
lean_dec(x_316);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_2);
lean_ctor_set(x_321, 2, x_3);
lean_ctor_set(x_321, 3, x_318);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_318, x_2, x_3);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_317);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
lean_object* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_318, x_2, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
return x_325;
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 2);
lean_inc(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_328);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_316);
lean_ctor_set(x_334, 2, x_317);
lean_ctor_set(x_334, 3, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_327, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
x_344 = 1;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_315);
lean_ctor_set(x_345, 1, x_316);
lean_ctor_set(x_345, 2, x_317);
lean_ctor_set(x_345, 3, x_326);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_338)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_338;
}
lean_ctor_set(x_346, 0, x_339);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_341);
lean_ctor_set(x_346, 3, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_337);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_325, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 2);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
x_351 = 0;
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(1, 4, 1);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_326);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_353, 0, x_315);
lean_ctor_set(x_353, 1, x_316);
lean_ctor_set(x_353, 2, x_317);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_358 = x_325;
} else {
 lean_dec_ref(x_325);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_326, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_326, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_326, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_363 = x_326;
} else {
 lean_dec_ref(x_326);
 x_363 = lean_box(0);
}
x_364 = 1;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_315);
lean_ctor_set(x_365, 1, x_316);
lean_ctor_set(x_365, 2, x_317);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_358;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set(x_366, 3, x_357);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_361);
lean_ctor_set(x_367, 3, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_325, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_325, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_325, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_371 = x_325;
} else {
 lean_dec_ref(x_325);
 x_371 = lean_box(0);
}
x_372 = 0;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_326);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_370);
lean_ctor_set(x_373, 3, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_316);
lean_ctor_set(x_374, 2, x_317);
lean_ctor_set(x_374, 3, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_325, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_325, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_378 = x_325;
} else {
 lean_dec_ref(x_325);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_368, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
lean_inc(x_326);
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_315);
lean_ctor_set(x_384, 1, x_316);
lean_ctor_set(x_384, 2, x_317);
lean_ctor_set(x_384, 3, x_326);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_385 = x_326;
} else {
 lean_dec_ref(x_326);
 x_385 = lean_box(0);
}
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_378)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_378;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_376);
lean_ctor_set(x_387, 2, x_377);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; 
x_388 = lean_ctor_get(x_325, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_325, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_390 = x_325;
} else {
 lean_dec_ref(x_325);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_326, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_326, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_326, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_326, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_395 = x_326;
} else {
 lean_dec_ref(x_326);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_391);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_393);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_388);
lean_ctor_set(x_398, 2, x_389);
lean_ctor_set(x_398, 3, x_368);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_315);
lean_ctor_set(x_399, 1, x_316);
lean_ctor_set(x_399, 2, x_317);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_375);
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
uint8_t x_400; 
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_315, x_2, x_3);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_316);
lean_ctor_set(x_402, 2, x_317);
lean_ctor_set(x_402, 3, x_318);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
lean_object* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_315, x_2, x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
return x_403;
}
else
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = 0;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set(x_410, 2, x_407);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_316);
lean_ctor_set(x_412, 2, x_317);
lean_ctor_set(x_412, 3, x_318);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8_t x_413; 
x_413 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_403, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_405, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 2);
lean_inc(x_419);
x_420 = lean_ctor_get(x_405, 3);
lean_inc(x_420);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_421 = x_405;
} else {
 lean_dec_ref(x_405);
 x_421 = lean_box(0);
}
x_422 = 1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_417);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean_is_scalar(x_416)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_416;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_316);
lean_ctor_set(x_424, 2, x_317);
lean_ctor_set(x_424, 3, x_318);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_418);
lean_ctor_set(x_425, 2, x_419);
lean_ctor_set(x_425, 3, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_403, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_403, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_428 = x_403;
} else {
 lean_dec_ref(x_403);
 x_428 = lean_box(0);
}
x_429 = 0;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_404);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_427);
lean_ctor_set(x_430, 3, x_405);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_316);
lean_ctor_set(x_431, 2, x_317);
lean_ctor_set(x_431, 3, x_318);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_403, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_403, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_403, 3);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_404, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_404, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_404, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_404, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_441 = x_404;
} else {
 lean_dec_ref(x_404);
 x_441 = lean_box(0);
}
x_442 = 1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set(x_443, 2, x_439);
lean_ctor_set(x_443, 3, x_440);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_436;
}
lean_ctor_set(x_444, 0, x_435);
lean_ctor_set(x_444, 1, x_316);
lean_ctor_set(x_444, 2, x_317);
lean_ctor_set(x_444, 3, x_318);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_403, 3);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_403, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_403, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_449 = x_403;
} else {
 lean_dec_ref(x_403);
 x_449 = lean_box(0);
}
x_450 = 0;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_447);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_316);
lean_ctor_set(x_452, 2, x_317);
lean_ctor_set(x_452, 3, x_318);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = lean_ctor_get_uint8(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_403, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_456 = x_403;
} else {
 lean_dec_ref(x_403);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_461 = x_446;
} else {
 lean_dec_ref(x_446);
 x_461 = lean_box(0);
}
lean_inc(x_404);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_457);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_463 = x_404;
} else {
 lean_dec_ref(x_404);
 x_463 = lean_box(0);
}
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_316);
lean_ctor_set(x_464, 2, x_317);
lean_ctor_set(x_464, 3, x_318);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 4, 1);
} else {
 x_465 = x_456;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_459);
lean_ctor_set(x_465, 3, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_403, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_403, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_468 = x_403;
} else {
 lean_dec_ref(x_403);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_404, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_404, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_404, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_473 = x_404;
} else {
 lean_dec_ref(x_404);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_469);
lean_ctor_set(x_474, 1, x_470);
lean_ctor_set(x_474, 2, x_471);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean_is_scalar(x_468)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_468;
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_466);
lean_ctor_set(x_476, 2, x_467);
lean_ctor_set(x_476, 3, x_446);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_316);
lean_ctor_set(x_477, 2, x_317);
lean_ctor_set(x_477, 3, x_318);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_453);
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
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
else
{
lean_object* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_19, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_16, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isRed___rarg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_31, x_2, x_3);
lean_ctor_set(x_1, 3, x_35);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_31, x_2, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_free_object(x_1);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = 0;
lean_ctor_set(x_36, 0, x_38);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 2);
x_53 = lean_ctor_get(x_36, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
x_60 = 1;
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_60);
lean_ctor_set(x_36, 3, x_59);
lean_ctor_set(x_36, 2, x_58);
lean_ctor_set(x_36, 1, x_57);
lean_ctor_set(x_36, 0, x_56);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_60);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_65 = 1;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_29);
lean_ctor_set(x_66, 2, x_30);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
lean_ctor_set(x_36, 3, x_64);
lean_ctor_set(x_36, 2, x_63);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_61);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_65);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_52);
lean_ctor_set(x_1, 1, x_51);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_36);
x_69 = lean_ctor_get(x_38, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = 1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 4, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_28);
lean_ctor_set(x_75, 1, x_29);
lean_ctor_set(x_75, 2, x_30);
lean_ctor_set(x_75, 3, x_37);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_68);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_36, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_36, 0);
lean_dec(x_79);
x_80 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_36, 1);
x_82 = lean_ctor_get(x_36, 2);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set(x_84, 3, x_38);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
lean_ctor_set(x_1, 3, x_84);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_36);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
x_91 = lean_ctor_get(x_37, 2);
x_92 = lean_ctor_get(x_37, 3);
x_93 = 1;
lean_ctor_set(x_37, 3, x_89);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_93);
lean_ctor_set(x_36, 0, x_92);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
x_96 = lean_ctor_get(x_37, 2);
x_97 = lean_ctor_get(x_37, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
x_98 = 1;
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_28);
lean_ctor_set(x_99, 1, x_29);
lean_ctor_set(x_99, 2, x_30);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_98);
lean_ctor_set(x_36, 0, x_97);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_98);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set(x_1, 2, x_96);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_99);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_36, 1);
x_101 = lean_ctor_get(x_36, 2);
x_102 = lean_ctor_get(x_36, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_103 = lean_ctor_get(x_37, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_107 = x_37;
} else {
 lean_dec_ref(x_37);
 x_107 = lean_box(0);
}
x_108 = 1;
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_28);
lean_ctor_set(x_109, 1, x_29);
lean_ctor_set(x_109, 2, x_30);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_100);
lean_ctor_set(x_110, 2, x_101);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_110);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_36, 3);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_36, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_36, 0);
lean_dec(x_114);
x_115 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_36, 1);
x_117 = lean_ctor_get(x_36, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = 0;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_1);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_36, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 0);
lean_dec(x_123);
x_124 = !lean_is_exclusive(x_111);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_111, 0);
x_126 = lean_ctor_get(x_111, 1);
x_127 = lean_ctor_get(x_111, 2);
x_128 = lean_ctor_get(x_111, 3);
lean_inc(x_37);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set(x_111, 2, x_30);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_28);
x_129 = !lean_is_exclusive(x_37);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_37, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_37, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_37, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
lean_ctor_set(x_37, 3, x_128);
lean_ctor_set(x_37, 2, x_127);
lean_ctor_set(x_37, 1, x_126);
lean_ctor_set(x_37, 0, x_125);
lean_ctor_set(x_36, 3, x_37);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
lean_object* x_134; 
lean_dec(x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_85);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_134);
lean_ctor_set(x_36, 0, x_111);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_111, 0);
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_111);
lean_inc(x_37);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_28);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_140 = x_37;
} else {
 lean_dec_ref(x_37);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_85);
lean_ctor_set(x_36, 3, x_141);
lean_ctor_set(x_36, 0, x_139);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_36, 1);
x_143 = lean_ctor_get(x_36, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_ctor_get(x_111, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_111, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_111, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_111, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 x_148 = x_111;
} else {
 lean_dec_ref(x_111);
 x_148 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_29);
lean_ctor_set(x_149, 2, x_30);
lean_ctor_set(x_149, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_150 = x_37;
} else {
 lean_dec_ref(x_37);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_85);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_85);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_142);
lean_ctor_set(x_152, 2, x_143);
lean_ctor_set(x_152, 3, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_36);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_36, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_36, 0);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_37, 0);
x_159 = lean_ctor_get(x_37, 1);
x_160 = lean_ctor_get(x_37, 2);
x_161 = lean_ctor_get(x_37, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_37);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean_ctor_set(x_36, 0, x_162);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_163);
lean_ctor_set(x_1, 3, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_36, 1);
x_165 = lean_ctor_get(x_36, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_36);
x_166 = lean_ctor_get(x_37, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_37, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_37, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_37, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_170 = x_37;
} else {
 lean_dec_ref(x_37);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_111);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
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
uint8_t x_174; 
x_174 = l_RBNode_isRed___rarg(x_28);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_28, x_2, x_3);
lean_ctor_set(x_1, 0, x_175);
return x_1;
}
else
{
lean_object* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_28, x_2, x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_free_object(x_1);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_176;
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 3);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_176, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_176, 0);
lean_dec(x_181);
x_182 = 0;
lean_ctor_set(x_176, 0, x_178);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_176, 1);
x_185 = lean_ctor_get(x_176, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_176);
x_186 = 0;
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_178);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8_t x_189; 
x_189 = lean_ctor_get_uint8(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_176, 1);
x_192 = lean_ctor_get(x_176, 2);
x_193 = lean_ctor_get(x_176, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_176, 0);
lean_dec(x_194);
x_195 = !lean_is_exclusive(x_178);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = lean_ctor_get(x_178, 1);
x_198 = lean_ctor_get(x_178, 2);
x_199 = lean_ctor_get(x_178, 3);
x_200 = 1;
lean_ctor_set(x_178, 3, x_196);
lean_ctor_set(x_178, 2, x_192);
lean_ctor_set(x_178, 1, x_191);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_200);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_199);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_200);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_198);
lean_ctor_set(x_1, 1, x_197);
lean_ctor_set(x_1, 0, x_178);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_178, 0);
x_202 = lean_ctor_get(x_178, 1);
x_203 = lean_ctor_get(x_178, 2);
x_204 = lean_ctor_get(x_178, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_178);
x_205 = 1;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_177);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_204);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_205);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_203);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_176, 1);
x_208 = lean_ctor_get(x_176, 2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_176);
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_178, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_178, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 x_213 = x_178;
} else {
 lean_dec_ref(x_178);
 x_213 = lean_box(0);
}
x_214 = 1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_177);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_208);
lean_ctor_set(x_215, 3, x_209);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_29);
lean_ctor_set(x_216, 2, x_30);
lean_ctor_set(x_216, 3, x_31);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_214);
lean_ctor_set(x_1, 3, x_216);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_176);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_176, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_176, 0);
lean_dec(x_219);
x_220 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_220);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_176, 1);
x_222 = lean_ctor_get(x_176, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_177);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_227 = lean_ctor_get(x_176, 1);
x_228 = lean_ctor_get(x_176, 2);
x_229 = lean_ctor_get(x_176, 3);
x_230 = lean_ctor_get(x_176, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_177);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = 1;
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_232);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_177);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_233 = lean_ctor_get(x_177, 0);
x_234 = lean_ctor_get(x_177, 1);
x_235 = lean_ctor_get(x_177, 2);
x_236 = lean_ctor_get(x_177, 3);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_177);
x_237 = 1;
x_238 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_237);
lean_ctor_set(x_176, 3, x_31);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 1, x_29);
lean_ctor_set(x_176, 0, x_229);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_237);
lean_ctor_set(x_1, 3, x_176);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_176, 1);
x_240 = lean_ctor_get(x_176, 2);
x_241 = lean_ctor_get(x_176, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_176);
x_242 = lean_ctor_get(x_177, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_177, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_177, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_177, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_246 = x_177;
} else {
 lean_dec_ref(x_177);
 x_246 = lean_box(0);
}
x_247 = 1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_242);
lean_ctor_set(x_248, 1, x_243);
lean_ctor_set(x_248, 2, x_244);
lean_ctor_set(x_248, 3, x_245);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_29);
lean_ctor_set(x_249, 2, x_30);
lean_ctor_set(x_249, 3, x_31);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_249);
lean_ctor_set(x_1, 2, x_240);
lean_ctor_set(x_1, 1, x_239);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_176, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_176, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_176, 0);
lean_dec(x_253);
x_254 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_254);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_176, 1);
x_256 = lean_ctor_get(x_176, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_176);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_177);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8_t x_260; 
lean_free_object(x_1);
x_260 = !lean_is_exclusive(x_176);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_261 = lean_ctor_get(x_176, 1);
x_262 = lean_ctor_get(x_176, 2);
x_263 = lean_ctor_get(x_176, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_176, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
x_268 = lean_ctor_get(x_250, 2);
x_269 = lean_ctor_get(x_250, 3);
lean_inc(x_177);
lean_ctor_set(x_250, 3, x_266);
lean_ctor_set(x_250, 2, x_262);
lean_ctor_set(x_250, 1, x_261);
lean_ctor_set(x_250, 0, x_177);
x_270 = !lean_is_exclusive(x_177);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_177, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_177, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_177, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_177, 0);
lean_dec(x_274);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
lean_ctor_set(x_177, 3, x_31);
lean_ctor_set(x_177, 2, x_30);
lean_ctor_set(x_177, 1, x_29);
lean_ctor_set(x_177, 0, x_269);
lean_ctor_set(x_176, 3, x_177);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
lean_object* x_275; 
lean_dec(x_177);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_225);
x_275 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_29);
lean_ctor_set(x_275, 2, x_30);
lean_ctor_set(x_275, 3, x_31);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_275);
lean_ctor_set(x_176, 2, x_268);
lean_ctor_set(x_176, 1, x_267);
lean_ctor_set(x_176, 0, x_250);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_250, 0);
x_277 = lean_ctor_get(x_250, 1);
x_278 = lean_ctor_get(x_250, 2);
x_279 = lean_ctor_get(x_250, 3);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_250);
lean_inc(x_177);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_177);
lean_ctor_set(x_280, 1, x_261);
lean_ctor_set(x_280, 2, x_262);
lean_ctor_set(x_280, 3, x_276);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_281 = x_177;
} else {
 lean_dec_ref(x_177);
 x_281 = lean_box(0);
}
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 4, 1);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_29);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_31);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_225);
lean_ctor_set(x_176, 3, x_282);
lean_ctor_set(x_176, 2, x_278);
lean_ctor_set(x_176, 1, x_277);
lean_ctor_set(x_176, 0, x_280);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_176, 1);
x_284 = lean_ctor_get(x_176, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_176);
x_285 = lean_ctor_get(x_250, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_250, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_250, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_250, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_289 = x_250;
} else {
 lean_dec_ref(x_250);
 x_289 = lean_box(0);
}
lean_inc(x_177);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_177);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_285);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_291 = x_177;
} else {
 lean_dec_ref(x_177);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_225);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_29);
lean_ctor_set(x_292, 2, x_30);
lean_ctor_set(x_292, 3, x_31);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_225);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_286);
lean_ctor_set(x_293, 2, x_287);
lean_ctor_set(x_293, 3, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_176);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_176, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_176, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_177);
if (x_297 == 0)
{
uint8_t x_298; 
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_299 = lean_ctor_get(x_177, 0);
x_300 = lean_ctor_get(x_177, 1);
x_301 = lean_ctor_get(x_177, 2);
x_302 = lean_ctor_get(x_177, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_177);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean_ctor_set(x_176, 0, x_303);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_304);
lean_ctor_set(x_1, 0, x_176);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_305 = lean_ctor_get(x_176, 1);
x_306 = lean_ctor_get(x_176, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_176);
x_307 = lean_ctor_get(x_177, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_177, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_177, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_177, 3);
lean_inc(x_310);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_311 = x_177;
} else {
 lean_dec_ref(x_177);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 4, 1);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_307);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_309);
lean_ctor_set(x_312, 3, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_306);
lean_ctor_set(x_314, 3, x_250);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
lean_ctor_set(x_1, 0, x_314);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
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
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_ctor_get(x_1, 1);
x_317 = lean_ctor_get(x_1, 2);
x_318 = lean_ctor_get(x_1, 3);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_317);
lean_dec(x_316);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_315);
lean_ctor_set(x_321, 1, x_2);
lean_ctor_set(x_321, 2, x_3);
lean_ctor_set(x_321, 3, x_318);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8_t x_322; 
x_322 = l_RBNode_isRed___rarg(x_318);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_318, x_2, x_3);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_317);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
lean_object* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_318, x_2, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
return x_325;
}
else
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_325, 3);
lean_inc(x_327);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 2);
lean_inc(x_329);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_330 = x_325;
} else {
 lean_dec_ref(x_325);
 x_330 = lean_box(0);
}
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_328);
lean_ctor_set(x_332, 2, x_329);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_315);
lean_ctor_set(x_334, 1, x_316);
lean_ctor_set(x_334, 2, x_317);
lean_ctor_set(x_334, 3, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = lean_ctor_get_uint8(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 2);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_327, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_327, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
x_344 = 1;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_315);
lean_ctor_set(x_345, 1, x_316);
lean_ctor_set(x_345, 2, x_317);
lean_ctor_set(x_345, 3, x_326);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_338)) {
 x_346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_346 = x_338;
}
lean_ctor_set(x_346, 0, x_339);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_341);
lean_ctor_set(x_346, 3, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_344);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_337);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_325, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 2);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
x_351 = 0;
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(1, 4, 1);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_326);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_349);
lean_ctor_set(x_352, 3, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_351);
x_353 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_353, 0, x_315);
lean_ctor_set(x_353, 1, x_316);
lean_ctor_set(x_353, 2, x_317);
lean_ctor_set(x_353, 3, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_358 = x_325;
} else {
 lean_dec_ref(x_325);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_326, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_326, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_326, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_363 = x_326;
} else {
 lean_dec_ref(x_326);
 x_363 = lean_box(0);
}
x_364 = 1;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_315);
lean_ctor_set(x_365, 1, x_316);
lean_ctor_set(x_365, 2, x_317);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_358;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set(x_366, 3, x_357);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_364);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_360);
lean_ctor_set(x_367, 2, x_361);
lean_ctor_set(x_367, 3, x_366);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_325, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_369 = lean_ctor_get(x_325, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_325, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_371 = x_325;
} else {
 lean_dec_ref(x_325);
 x_371 = lean_box(0);
}
x_372 = 0;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_326);
lean_ctor_set(x_373, 1, x_369);
lean_ctor_set(x_373, 2, x_370);
lean_ctor_set(x_373, 3, x_368);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_315);
lean_ctor_set(x_374, 1, x_316);
lean_ctor_set(x_374, 2, x_317);
lean_ctor_set(x_374, 3, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_376 = lean_ctor_get(x_325, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_325, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_378 = x_325;
} else {
 lean_dec_ref(x_325);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_368, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_368, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
lean_inc(x_326);
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_315);
lean_ctor_set(x_384, 1, x_316);
lean_ctor_set(x_384, 2, x_317);
lean_ctor_set(x_384, 3, x_326);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_385 = x_326;
} else {
 lean_dec_ref(x_326);
 x_385 = lean_box(0);
}
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_378)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_378;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_376);
lean_ctor_set(x_387, 2, x_377);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; 
x_388 = lean_ctor_get(x_325, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_325, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 x_390 = x_325;
} else {
 lean_dec_ref(x_325);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_326, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_326, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_326, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_326, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 x_395 = x_326;
} else {
 lean_dec_ref(x_326);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_391);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_396, 2, x_393);
lean_ctor_set(x_396, 3, x_394);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_388);
lean_ctor_set(x_398, 2, x_389);
lean_ctor_set(x_398, 3, x_368);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_315);
lean_ctor_set(x_399, 1, x_316);
lean_ctor_set(x_399, 2, x_317);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_375);
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
uint8_t x_400; 
x_400 = l_RBNode_isRed___rarg(x_315);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_315, x_2, x_3);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_316);
lean_ctor_set(x_402, 2, x_317);
lean_ctor_set(x_402, 3, x_318);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
lean_object* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_315, x_2, x_3);
if (lean_obj_tag(x_403) == 0)
{
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
return x_403;
}
else
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 2);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = 0;
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_406);
lean_ctor_set(x_410, 2, x_407);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_316);
lean_ctor_set(x_412, 2, x_317);
lean_ctor_set(x_412, 3, x_318);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8_t x_413; 
x_413 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_414 = lean_ctor_get(x_403, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 2);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_405, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_405, 2);
lean_inc(x_419);
x_420 = lean_ctor_get(x_405, 3);
lean_inc(x_420);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_421 = x_405;
} else {
 lean_dec_ref(x_405);
 x_421 = lean_box(0);
}
x_422 = 1;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_417);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
if (lean_is_scalar(x_416)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_416;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_316);
lean_ctor_set(x_424, 2, x_317);
lean_ctor_set(x_424, 3, x_318);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_422);
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_418);
lean_ctor_set(x_425, 2, x_419);
lean_ctor_set(x_425, 3, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_403, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_403, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_428 = x_403;
} else {
 lean_dec_ref(x_403);
 x_428 = lean_box(0);
}
x_429 = 0;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(1, 4, 1);
} else {
 x_430 = x_428;
}
lean_ctor_set(x_430, 0, x_404);
lean_ctor_set(x_430, 1, x_426);
lean_ctor_set(x_430, 2, x_427);
lean_ctor_set(x_430, 3, x_405);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_316);
lean_ctor_set(x_431, 2, x_317);
lean_ctor_set(x_431, 3, x_318);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8_t x_432; 
x_432 = lean_ctor_get_uint8(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_403, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_403, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_403, 3);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_404, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_404, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_404, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_404, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_441 = x_404;
} else {
 lean_dec_ref(x_404);
 x_441 = lean_box(0);
}
x_442 = 1;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_438);
lean_ctor_set(x_443, 2, x_439);
lean_ctor_set(x_443, 3, x_440);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_436;
}
lean_ctor_set(x_444, 0, x_435);
lean_ctor_set(x_444, 1, x_316);
lean_ctor_set(x_444, 2, x_317);
lean_ctor_set(x_444, 3, x_318);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_442);
x_445 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_403, 3);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_403, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_403, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_449 = x_403;
} else {
 lean_dec_ref(x_403);
 x_449 = lean_box(0);
}
x_450 = 0;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_447);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_446);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_316);
lean_ctor_set(x_452, 2, x_317);
lean_ctor_set(x_452, 3, x_318);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8_t x_453; 
x_453 = lean_ctor_get_uint8(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_403, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_456 = x_403;
} else {
 lean_dec_ref(x_403);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_446, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_446, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_446, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 lean_ctor_release(x_446, 3);
 x_461 = x_446;
} else {
 lean_dec_ref(x_446);
 x_461 = lean_box(0);
}
lean_inc(x_404);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_457);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_463 = x_404;
} else {
 lean_dec_ref(x_404);
 x_463 = lean_box(0);
}
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_316);
lean_ctor_set(x_464, 2, x_317);
lean_ctor_set(x_464, 3, x_318);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_432);
if (lean_is_scalar(x_456)) {
 x_465 = lean_alloc_ctor(1, 4, 1);
} else {
 x_465 = x_456;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_458);
lean_ctor_set(x_465, 2, x_459);
lean_ctor_set(x_465, 3, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_403, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_403, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 x_468 = x_403;
} else {
 lean_dec_ref(x_403);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_404, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_404, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_404, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 x_473 = x_404;
} else {
 lean_dec_ref(x_404);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_469);
lean_ctor_set(x_474, 1, x_470);
lean_ctor_set(x_474, 2, x_471);
lean_ctor_set(x_474, 3, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean_is_scalar(x_468)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_468;
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_466);
lean_ctor_set(x_476, 2, x_467);
lean_ctor_set(x_476, 3, x_446);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_316);
lean_ctor_set(x_477, 2, x_317);
lean_ctor_set(x_477, 3, x_318);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_453);
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
lean_object* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_1, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_TokenMap_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_insert___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_TokenMap_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Parser_TokenMap_HasEmptyc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_ParsingTables_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_ParsingTables_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParsingTables_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_currLbp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
x_4 = l_Lean_Parser_peekToken(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 1, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
switch (lean_obj_tag(x_12)) {
case 1:
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_4, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_numLitKind;
x_17 = lean_name_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_charLitKind;
x_19 = lean_name_dec_eq(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_strLitKind;
x_21 = lean_name_dec_eq(x_15, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_fieldIdxKind;
x_23 = lean_name_dec_eq(x_15, x_22);
lean_dec(x_15);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 1, x_24);
return x_4;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Parser_appPrec;
lean_ctor_set(x_4, 1, x_25);
return x_4;
}
}
else
{
lean_object* x_26; 
lean_dec(x_15);
x_26 = l_Lean_Parser_appPrec;
lean_ctor_set(x_4, 1, x_26);
return x_4;
}
}
else
{
lean_object* x_27; 
lean_dec(x_15);
x_27 = l_Lean_Parser_appPrec;
lean_ctor_set(x_4, 1, x_27);
return x_4;
}
}
else
{
lean_object* x_28; 
lean_dec(x_15);
x_28 = l_Lean_Parser_appPrec;
lean_ctor_set(x_4, 1, x_28);
return x_4;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = l_Lean_numLitKind;
x_32 = lean_name_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_charLitKind;
x_34 = lean_name_dec_eq(x_30, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_strLitKind;
x_36 = lean_name_dec_eq(x_30, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_fieldIdxKind;
x_38 = lean_name_dec_eq(x_30, x_37);
lean_dec(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Parser_appPrec;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_43 = l_Lean_Parser_appPrec;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_30);
x_45 = l_Lean_Parser_appPrec;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_30);
x_47 = l_Lean_Parser_appPrec;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_49 = lean_ctor_get(x_4, 0);
lean_inc(x_49);
lean_dec(x_4);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Parser_Trie_matchPrefix___rarg(x_50, x_52, x_53);
lean_dec(x_50);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 1);
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
if (lean_obj_tag(x_56) == 0)
{
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 2);
lean_inc(x_60);
lean_dec(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
lean_ctor_set(x_54, 1, x_61);
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
lean_dec(x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
lean_ctor_set(x_54, 1, x_63);
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Parser_checkTailNoWs(x_1);
if (x_66 == 0)
{
lean_dec(x_65);
lean_ctor_set(x_54, 1, x_64);
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
else
{
lean_dec(x_64);
lean_ctor_set(x_54, 1, x_65);
lean_ctor_set(x_54, 0, x_49);
return x_54;
}
}
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_dec(x_54);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_53);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 2);
lean_inc(x_71);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_49);
lean_ctor_set(x_72, 1, x_53);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_49);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_69, 2);
lean_inc(x_75);
lean_dec(x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_49);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = l_Lean_Parser_checkTailNoWs(x_1);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_49);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; 
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_49);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
}
}
}
case 3:
{
uint8_t x_83; 
lean_dec(x_12);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_4, 1);
lean_dec(x_84);
x_85 = l_Lean_Parser_appPrec;
lean_ctor_set(x_4, 1, x_85);
return x_4;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_4, 0);
lean_inc(x_86);
lean_dec(x_4);
x_87 = l_Lean_Parser_appPrec;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
default: 
{
uint8_t x_89; 
lean_dec(x_12);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_4);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_dec(x_90);
x_91 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 1, x_91);
return x_4;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
lean_dec(x_4);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
}
lean_object* l_Lean_Parser_currLbp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_currLbp(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_indexed___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Parser_peekToken(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
switch (lean_obj_tag(x_17)) {
case 1:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_8 = x_18;
goto block_14;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_name_mk_string(x_20, x_19);
x_8 = x_21;
goto block_14;
}
case 3:
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = l_Lean_Parser_indexed___rarg___closed__1;
x_8 = x_22;
goto block_14;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
block_14:
{
lean_object* x_9; 
x_9 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Parser_indexed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_indexed___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_indexed___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_7__mkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = lean_nat_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_nullKind;
x_9 = l_Lean_Parser_ParserState_mkNode(x_1, x_8, x_2);
return x_9;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Parser_leadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_9 = l_Lean_Parser_indexed___rarg(x_8, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_isEmpty___rarg(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = 0;
x_14 = l_Lean_Parser_longestMatchFn(x_13, x_11, x_3, x_4, x_10);
x_15 = l___private_Init_Lean_Parser_Parser_7__mkResult(x_14, x_7);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lean_Parser_ParserState_mkError(x_10, x_1);
return x_16;
}
}
}
lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_trailingLoopStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = 1;
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Parser_longestMatchFn(x_10, x_2, x_3, x_4, x_5);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_14, x_9);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_9);
x_16 = l_Lean_Parser_ParserState_restore(x_11, x_8, x_9);
lean_dec(x_8);
x_17 = l_Lean_Parser_anyOfFn___main(x_10, x_6, x_3, x_4, x_16);
x_18 = l_Lean_Parser_mergeOrElseErrors(x_17, x_13, x_9);
lean_dec(x_9);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_trailingLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
x_6 = l_Lean_Parser_currLbp(x_4, x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_8, x_2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = l_Lean_Parser_indexed___rarg(x_12, x_3, x_7);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_Parser_trailingLoopStep(x_1, x_15, x_4, x_3, x_14);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l___private_Init_Lean_Parser_Parser_7__mkResult(x_17, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_20);
lean_dec(x_20);
x_22 = l_Lean_Parser_ParserState_popSyntax(x_19);
x_4 = x_21;
x_5 = x_22;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = l_List_isEmpty___rarg(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_Parser_trailingLoopStep(x_1, x_15, x_4, x_3, x_14);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l___private_Init_Lean_Parser_Parser_7__mkResult(x_26, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_29);
lean_dec(x_29);
x_31 = l_Lean_Parser_ParserState_popSyntax(x_28);
x_4 = x_30;
x_5 = x_31;
goto _start;
}
else
{
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
}
else
{
lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_33 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_4);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_1);
x_34 = l_Lean_Parser_ParserState_pushSyntax(x_7, x_4);
return x_34;
}
}
}
lean_object* l_Lean_Parser_trailingLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_trailingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_trailingLoop___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_trailingLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_trailingLoop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_prattParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_11 = l_Lean_Parser_trailingLoop___main(x_2, x_3, x_4, x_9, x_10);
lean_dec(x_3);
return x_11;
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* l_Lean_Parser_mkBuiltinTokenTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkImportedTokenTable___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_builtinTokenTable;
x_3 = lean_io_ref_get(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Parser_mkImportedTokenTable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkImportedTokenTable___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_mkImportedTokenTable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkImportedTokenTable(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Parser_Trie_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Parser_TokenTableAttribute_inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_TokenTableAttribute_inhabited___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_Parser_TokenTableAttribute_inhabited___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_TokenTableAttribute_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_TokenTableAttribute_inhabited___closed__4;
return x_1;
}
}
lean_object* l_Lean_fmt___at_Lean_Parser_mkTokenTableAttribute___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_mk_string("failed to register environment, extensions can only be registered during initialization");
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_mk_string("failed to register environment, extensions can only be registered during initialization");
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 0, x_14);
x_15 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_16 = lean_io_ref_get(x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_io_ref_get(x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_27, 0, x_14);
x_30 = lean_io_ref_reset(x_15, x_27);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_14);
x_33 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_34 = l_Lean_EnvExtensionState_inhabited;
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_26);
x_36 = x_26;
x_37 = lean_array_push(x_29, x_36);
x_38 = lean_io_ref_set(x_15, x_37, x_30);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_26);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_50 = l_Lean_EnvExtensionState_inhabited;
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_26);
x_52 = x_26;
x_53 = lean_array_push(x_29, x_52);
x_54 = lean_io_ref_set(x_15, x_53, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_26);
x_62 = !lean_is_exclusive(x_30);
if (x_62 == 0)
{
return x_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_30, 0);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_30);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_27, 0);
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_27);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_io_ref_reset(x_15, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_14);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_74 = l_Lean_EnvExtensionState_inhabited;
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_20);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_26);
x_76 = x_26;
x_77 = lean_array_push(x_66, x_76);
x_78 = lean_io_ref_set(x_15, x_77, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_26);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_26);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_26);
x_86 = lean_ctor_get(x_69, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_88 = x_69;
} else {
 lean_dec_ref(x_69);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_26);
x_90 = !lean_is_exclusive(x_27);
if (x_90 == 0)
{
return x_27;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_27, 0);
x_92 = lean_ctor_get(x_27, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_27);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_94 = lean_ctor_get(x_16, 0);
x_95 = lean_ctor_get(x_16, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_16);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_14);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_get_size(x_94);
lean_dec(x_94);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_mk_empty_array_with_capacity(x_98);
x_100 = lean_box(0);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_1);
lean_ctor_set(x_104, 2, x_103);
x_105 = lean_io_ref_get(x_15, x_96);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_14);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_io_ref_reset(x_15, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_14);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_115 = l_Lean_EnvExtensionState_inhabited;
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_98);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_115);
lean_inc(x_104);
x_117 = x_104;
x_118 = lean_array_push(x_106, x_117);
x_119 = lean_io_ref_set(x_15, x_118, x_113);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_104);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_104);
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_125 = x_119;
} else {
 lean_dec_ref(x_119);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_106);
lean_dec(x_104);
x_127 = lean_ctor_get(x_110, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_110, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_129 = x_110;
} else {
 lean_dec_ref(x_110);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_104);
x_131 = lean_ctor_get(x_105, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_105, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_133 = x_105;
} else {
 lean_dec_ref(x_105);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_16);
if (x_135 == 0)
{
return x_16;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_16, 0);
x_137 = lean_ctor_get(x_16, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_16);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_3, 1);
lean_inc(x_139);
lean_dec(x_3);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_143 = lean_io_ref_get(x_142, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_140);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_array_get_size(x_144);
lean_dec(x_144);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_mk_empty_array_with_capacity(x_149);
x_151 = lean_box(0);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_1);
lean_ctor_set(x_155, 2, x_154);
x_156 = lean_io_ref_get(x_142, x_147);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_140);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_io_ref_reset(x_142, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_140);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_closure((void*)(l_Lean_EnvExtension_Inhabited___rarg___lambda__1), 1, 0);
x_166 = l_Lean_EnvExtensionState_inhabited;
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_149);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_166);
lean_inc(x_155);
x_168 = x_155;
x_169 = lean_array_push(x_157, x_168);
x_170 = lean_io_ref_set(x_142, x_169, x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_155);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_155);
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_157);
lean_dec(x_155);
x_178 = lean_ctor_get(x_161, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_161, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_180 = x_161;
} else {
 lean_dec_ref(x_161);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_155);
x_182 = lean_ctor_get(x_156, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_156, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_184 = x_156;
} else {
 lean_dec_ref(x_156);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_1);
x_186 = lean_ctor_get(x_143, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_143, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_188 = x_143;
} else {
 lean_dec_ref(x_143);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_3);
if (x_190 == 0)
{
return x_3;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_3, 0);
x_192 = lean_ctor_get(x_3, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_3);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3(x_1, x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_mk_empty_array_with_capacity(x_7);
lean_inc(x_10);
lean_inc(x_11);
x_12 = lean_apply_1(x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1), 3, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__4(x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_9);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_io_ref_get(x_3, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_9);
x_26 = lean_io_ref_reset(x_3, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_9);
x_29 = l_Lean_EnvExtensionState_inhabited;
x_30 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_29);
lean_inc(x_22);
x_31 = x_22;
x_32 = lean_array_push(x_25, x_31);
x_33 = lean_io_ref_set(x_3, x_32, x_26);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_22);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_22);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_EnvExtensionState_inhabited;
x_45 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_44);
lean_inc(x_22);
x_46 = x_22;
x_47 = lean_array_push(x_25, x_46);
x_48 = lean_io_ref_set(x_3, x_47, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_22);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_22);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_54 = x_48;
} else {
 lean_dec_ref(x_48);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_25);
lean_dec(x_22);
x_56 = !lean_is_exclusive(x_26);
if (x_56 == 0)
{
return x_26;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_26, 0);
x_58 = lean_ctor_get(x_26, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_26);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_23, 0);
x_61 = lean_ctor_get(x_23, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_23);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_9);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_io_ref_reset(x_3, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_EnvExtensionState_inhabited;
x_68 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_67);
lean_inc(x_22);
x_69 = x_22;
x_70 = lean_array_push(x_60, x_69);
x_71 = lean_io_ref_set(x_3, x_70, x_66);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_22);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_60);
lean_dec(x_22);
x_79 = lean_ctor_get(x_63, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_63, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_81 = x_63;
} else {
 lean_dec_ref(x_63);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_22);
x_83 = !lean_is_exclusive(x_23);
if (x_83 == 0)
{
return x_23;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_23, 0);
x_85 = lean_ctor_get(x_23, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_23);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_15, 0);
x_88 = lean_ctor_get(x_15, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_15);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_9);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 4);
lean_inc(x_93);
lean_dec(x_1);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_10);
lean_ctor_set(x_94, 3, x_91);
lean_ctor_set(x_94, 4, x_92);
lean_ctor_set(x_94, 5, x_93);
x_95 = lean_io_ref_get(x_3, x_89);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_9);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_io_ref_reset(x_3, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_9);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_EnvExtensionState_inhabited;
x_105 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_104);
lean_inc(x_94);
x_106 = x_94;
x_107 = lean_array_push(x_96, x_106);
x_108 = lean_io_ref_set(x_3, x_107, x_103);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_94);
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_96);
lean_dec(x_94);
x_116 = lean_ctor_get(x_100, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_100, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_118 = x_100;
} else {
 lean_dec_ref(x_100);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_94);
x_120 = lean_ctor_get(x_95, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_95, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_122 = x_95;
} else {
 lean_dec_ref(x_95);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_10);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_15);
if (x_124 == 0)
{
return x_15;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_15, 0);
x_126 = lean_ctor_get(x_15, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_15);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
lean_dec(x_1);
x_129 = lean_mk_string(".");
x_130 = l_Lean_Name_toStringWithSep___main(x_129, x_128);
lean_dec(x_129);
x_131 = lean_mk_string("invalid environment extension, '");
x_132 = lean_string_append(x_131, x_130);
lean_dec(x_130);
x_133 = lean_mk_string("' has already been used");
x_134 = lean_string_append(x_132, x_133);
lean_dec(x_133);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_134);
return x_4;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_4, 0);
x_136 = lean_ctor_get(x_4, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_4);
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3(x_1, x_135, x_137);
lean_dec(x_135);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
x_141 = lean_ctor_get(x_1, 1);
lean_inc(x_141);
x_142 = lean_mk_empty_array_with_capacity(x_137);
lean_inc(x_141);
lean_inc(x_142);
x_143 = lean_apply_1(x_141, x_142);
x_144 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__1), 3, 1);
lean_closure_set(x_144, 0, x_142);
x_145 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_145, 0, x_143);
lean_closure_set(x_145, 1, x_144);
x_146 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__4(x_145, x_140);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_148);
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_1, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_1, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 4);
lean_inc(x_154);
lean_dec(x_1);
x_155 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_155, 0, x_147);
lean_ctor_set(x_155, 1, x_151);
lean_ctor_set(x_155, 2, x_141);
lean_ctor_set(x_155, 3, x_152);
lean_ctor_set(x_155, 4, x_153);
lean_ctor_set(x_155, 5, x_154);
x_156 = lean_io_ref_get(x_3, x_150);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_139);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_io_ref_reset(x_3, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_139);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_EnvExtensionState_inhabited;
x_166 = l_Lean_PersistentEnvExtension_inhabited___rarg(x_165);
lean_inc(x_155);
x_167 = x_155;
x_168 = lean_array_push(x_157, x_167);
x_169 = lean_io_ref_set(x_3, x_168, x_164);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_155);
x_173 = lean_ctor_get(x_169, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_175 = x_169;
} else {
 lean_dec_ref(x_169);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_157);
lean_dec(x_155);
x_177 = lean_ctor_get(x_161, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_161, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_179 = x_161;
} else {
 lean_dec_ref(x_161);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_155);
x_181 = lean_ctor_get(x_156, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_156, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_183 = x_156;
} else {
 lean_dec_ref(x_156);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_141);
lean_dec(x_1);
x_185 = lean_ctor_get(x_146, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_146, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_187 = x_146;
} else {
 lean_dec_ref(x_146);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = lean_ctor_get(x_1, 0);
lean_inc(x_189);
lean_dec(x_1);
x_190 = lean_mk_string(".");
x_191 = l_Lean_Name_toStringWithSep___main(x_190, x_189);
lean_dec(x_190);
x_192 = lean_mk_string("invalid environment extension, '");
x_193 = lean_string_append(x_192, x_191);
lean_dec(x_191);
x_194 = lean_mk_string("' has already been used");
x_195 = lean_string_append(x_193, x_194);
lean_dec(x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_136);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_4);
if (x_197 == 0)
{
return x_4;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_4, 0);
x_199 = lean_ctor_get(x_4, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_4);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_mkImportedTokenTable___rarg(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string("token table attribute");
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkTokenTableAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_box(0);
x_3 = lean_mk_string("_tokens_");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_mkTokenTableAttribute___lambda__1___boxed), 2, 0);
x_6 = lean_alloc_closure((void*)(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed), 1, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_mkTokenTableAttribute___lambda__2___boxed), 1, 0);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_mkTokenTableAttribute___spec__2(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_13, 0, x_4);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_14, 0, x_4);
x_15 = lean_mk_string("internal token table attribute");
x_16 = lean_alloc_closure((void*)(l_Lean_AttributeImpl_inhabited___lambda__1___boxed), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_AttributeImpl_inhabited___lambda__4___boxed), 3, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_AttributeImpl_inhabited___lambda__5), 2, 0);
x_19 = 0;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_14);
lean_ctor_set(x_20, 5, x_17);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*8, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
lean_inc(x_4);
x_24 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_24, 0, x_4);
lean_inc(x_4);
x_25 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_25, 0, x_4);
x_26 = lean_mk_string("internal token table attribute");
x_27 = lean_alloc_closure((void*)(l_Lean_AttributeImpl_inhabited___lambda__1___boxed), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_AttributeImpl_inhabited___lambda__4___boxed), 3, 0);
x_29 = lean_alloc_closure((void*)(l_Lean_AttributeImpl_inhabited___lambda__5), 2, 0);
x_30 = 0;
lean_inc(x_29);
x_31 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_24);
lean_ctor_set(x_31, 4, x_25);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set(x_31, 6, x_29);
lean_ctor_set(x_31, 7, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*8, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Parser_mkTokenTableAttribute___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_mkTokenTableAttribute___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkTokenTableAttribute___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkTokenTableAttribute___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_Parser_mkSyntaxNodeKindSetRef___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Parser_mkSyntaxNodeKindSetRef___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkSyntaxNodeKindSetRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_mkSyntaxNodeKindSetRef___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_updateSyntaxNodeKinds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Parser_syntaxNodeKindSetRef;
x_5 = lean_io_ref_get(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_io_ref_reset(x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
x_12 = lean_apply_1(x_3, x_7);
x_13 = lean_io_ref_set(x_4, x_12, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_apply_1(x_3, x_7);
x_17 = lean_io_ref_set(x_4, x_16, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_io_ref_reset(x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_apply_1(x_3, x_22);
x_31 = lean_io_ref_set(x_4, x_30, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_22);
lean_dec(x_3);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
return x_5;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_5);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_Parser_nodeInfo___elambda__1___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_isValidSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_syntaxNodeKindSetRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_6, x_1);
lean_dec(x_6);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_9, x_1);
lean_dec(x_9);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Parser_isValidSyntaxNodeKind___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_isValidSyntaxNodeKind(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_Parser_getSyntaxNodeKinds___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_AssocList_mfoldl___main___at_Lean_Parser_getSyntaxNodeKinds___spec__1(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_syntaxNodeKindSetRef;
x_3 = lean_io_ref_get(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_5, x_7, x_8, x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_10, x_13, x_14, x_12);
lean_dec(x_13);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_Parser_getSyntaxNodeKinds___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_mfoldl___main___at_Lean_Parser_getSyntaxNodeKinds___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Parser_getSyntaxNodeKinds___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_mkParserContextCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_4 = l_Lean_FileMap_ofString(x_2);
x_5 = l_Lean_Parser_tokenTableAttribute;
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Lean_PersistentEnvExtension_getState___rarg(x_6, x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_mkParserContextCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_mkParserContextCore(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserContextCore_toParserContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkParserContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_mkParserContextCore(x_1, x_2, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_mkParserState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_runParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
x_6 = l_Lean_Parser_mkParserContext(x_1, x_3, x_4);
x_7 = l_Lean_Parser_mkParserState(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_whitespace___main(x_6, x_7);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_10 = l_Lean_Parser_prattParser(x_5, x_2, x_9, x_6, x_8);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = l_Lean_Parser_ParserState_toErrorMsg(x_6, x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Parser_mkBuiltinParsingTablesRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParsingTables_inhabited___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin parser '");
return x_1;
}
}
lean_object* l___private_Init_Lean_Parser_Parser_8__updateTokens(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Parser_builtinTokenTable;
x_5 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
x_6 = lean_io_ref_swap(x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_box(0);
lean_inc(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_11, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_2);
x_16 = l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_2);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_io_ref_set(x_4, x_22, x_6);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_box(0);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_apply_1(x_28, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_2);
x_33 = l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_registerTagAttribute___lambda__4___closed__4;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_30);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
lean_dec(x_2);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_io_ref_set(x_4, x_39, x_27);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_6);
if (x_41 == 0)
{
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_name_mk_string(x_7, x_6);
x_9 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_name_mk_string(x_13, x_12);
x_15 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_List_eraseDupsAux___main___at_Lean_Parser_addBuiltinLeadingParser___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_5, x_2);
if (x_7 == 0)
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
}
}
}
}
lean_object* l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_eraseDupsAux___main___at_Lean_Parser_addBuiltinLeadingParser___spec__3(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_8 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_4, x_1);
lean_ctor_set(x_2, 0, x_8);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_Parser_TokenMap_insert___rarg(x_10, x_4, x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
x_2 = x_14;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_8 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_4, x_1);
lean_ctor_set(x_2, 0, x_8);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_Parser_TokenMap_insert___rarg(x_10, x_4, x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
x_2 = x_14;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_Parser_addBuiltinLeadingParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', initial token is not statically known");
return x_1;
}
}
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_ref_get(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_io_ref_reset(x_1, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_12);
x_13 = l___private_Init_Lean_Parser_Parser_8__updateTokens(x_12, x_2, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_8);
lean_inc(x_12);
x_16 = l_Lean_Parser_updateSyntaxNodeKinds(x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
lean_inc(x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_17);
x_29 = lean_ctor_get(x_12, 2);
lean_inc(x_29);
lean_dec(x_12);
switch (lean_obj_tag(x_29)) {
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_30);
x_32 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_31);
x_33 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__5(x_3, x_7, x_32);
x_34 = lean_io_ref_set(x_1, x_33, x_28);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_35);
x_37 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_36);
x_38 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__6(x_3, x_7, x_37);
x_39 = lean_io_ref_set(x_1, x_38, x_28);
return x_39;
}
default: 
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_3);
x_19 = x_8;
goto block_27;
}
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_20 = l_System_FilePath_dirName___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_2);
x_22 = l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_25 = lean_string_append(x_23, x_24);
if (lean_is_scalar(x_18)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_18;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_12);
x_46 = l_Lean_Parser_updateSyntaxNodeKinds(x_12, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_58; lean_object* x_59; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
lean_inc(x_47);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_47);
x_59 = lean_ctor_get(x_12, 2);
lean_inc(x_59);
lean_dec(x_12);
switch (lean_obj_tag(x_59)) {
case 2:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_2);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_60);
x_62 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_61);
x_63 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__5(x_3, x_7, x_62);
x_64 = lean_io_ref_set(x_1, x_63, x_58);
return x_64;
}
case 3:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_2);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_65);
x_67 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_66);
x_68 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__6(x_3, x_7, x_67);
x_69 = lean_io_ref_set(x_1, x_68, x_58);
return x_69;
}
default: 
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_3);
x_49 = x_8;
goto block_57;
}
}
block_57:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
x_50 = l_System_FilePath_dirName___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_2);
x_52 = l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_55 = lean_string_append(x_53, x_54);
if (lean_is_scalar(x_48)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_48;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
return x_56;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_72 = x_46;
} else {
 lean_dec_ref(x_46);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_13);
if (x_74 == 0)
{
return x_13;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_13, 0);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_13);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_9, 1);
lean_inc(x_78);
lean_dec(x_9);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_ctor_get(x_3, 0);
lean_inc(x_80);
lean_inc(x_2);
lean_inc(x_80);
x_81 = l___private_Init_Lean_Parser_Parser_8__updateTokens(x_80, x_2, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_8);
lean_ctor_set(x_84, 1, x_82);
lean_inc(x_80);
x_85 = l_Lean_Parser_updateSyntaxNodeKinds(x_80, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_97; lean_object* x_98; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
lean_inc(x_86);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_86);
x_98 = lean_ctor_get(x_80, 2);
lean_inc(x_98);
lean_dec(x_80);
switch (lean_obj_tag(x_98)) {
case 2:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_99);
x_101 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_100);
x_102 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__5(x_3, x_7, x_101);
x_103 = lean_io_ref_set(x_1, x_102, x_97);
return x_103;
}
case 3:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_2);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
lean_dec(x_98);
x_105 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_104);
x_106 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_105);
x_107 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__6(x_3, x_7, x_106);
x_108 = lean_io_ref_set(x_1, x_107, x_97);
return x_108;
}
default: 
{
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_3);
x_88 = x_8;
goto block_96;
}
}
block_96:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_88);
x_89 = l_System_FilePath_dirName___closed__1;
x_90 = l_Lean_Name_toStringWithSep___main(x_89, x_2);
x_91 = l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_94 = lean_string_append(x_92, x_93);
if (lean_is_scalar(x_87)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_87;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_86);
return x_95;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_80);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_ctor_get(x_85, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_85, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_111 = x_85;
} else {
 lean_dec_ref(x_85);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_80);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_ctor_get(x_81, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_81, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_115 = x_81;
} else {
 lean_dec_ref(x_81);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_9);
if (x_117 == 0)
{
return x_9;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_9, 0);
x_119 = lean_ctor_get(x_9, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_9);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_5, 0);
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_5);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_io_ref_reset(x_1, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_ctor_get(x_3, 0);
lean_inc(x_129);
lean_inc(x_2);
lean_inc(x_129);
x_130 = l___private_Init_Lean_Parser_Parser_8__updateTokens(x_129, x_2, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_131);
lean_inc(x_129);
x_134 = l_Lean_Parser_updateSyntaxNodeKinds(x_129, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_146; lean_object* x_147; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
lean_inc(x_135);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_123);
lean_ctor_set(x_146, 1, x_135);
x_147 = lean_ctor_get(x_129, 2);
lean_inc(x_147);
lean_dec(x_129);
switch (lean_obj_tag(x_147)) {
case 2:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_148);
x_150 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_149);
x_151 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__5(x_3, x_121, x_150);
x_152 = lean_io_ref_set(x_1, x_151, x_146);
return x_152;
}
case 3:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
lean_dec(x_147);
x_154 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_153);
x_155 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_154);
x_156 = l_List_foldl___main___at_Lean_Parser_addBuiltinLeadingParser___spec__6(x_3, x_121, x_155);
x_157 = lean_io_ref_set(x_1, x_156, x_146);
return x_157;
}
default: 
{
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_121);
lean_dec(x_3);
x_137 = x_123;
goto block_145;
}
}
block_145:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_137);
x_138 = l_System_FilePath_dirName___closed__1;
x_139 = l_Lean_Name_toStringWithSep___main(x_138, x_2);
x_140 = l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l_Lean_Parser_addBuiltinLeadingParser___closed__1;
x_143 = lean_string_append(x_141, x_142);
if (lean_is_scalar(x_136)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_136;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_135);
return x_144;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_129);
lean_dec(x_121);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_ctor_get(x_134, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_134, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_160 = x_134;
} else {
 lean_dec_ref(x_134);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_129);
lean_dec(x_121);
lean_dec(x_3);
lean_dec(x_2);
x_162 = lean_ctor_get(x_130, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_130, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_164 = x_130;
} else {
 lean_dec_ref(x_130);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_121);
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_ctor_get(x_125, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_125, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_168 = x_125;
} else {
 lean_dec_ref(x_125);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_3);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_5);
if (x_170 == 0)
{
return x_5;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_5, 0);
x_172 = lean_ctor_get(x_5, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_5);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
lean_object* l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_addBuiltinLeadingParser(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_4, x_1);
lean_ctor_set(x_2, 1, x_8);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_Parser_TokenMap_insert___rarg(x_11, x_4, x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_12);
x_2 = x_14;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Parser_TokenMap_insert___rarg(x_7, x_4, x_1);
lean_ctor_set(x_2, 1, x_8);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_Parser_TokenMap_insert___rarg(x_11, x_4, x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_12);
x_2 = x_14;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_ref_get(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_io_ref_reset(x_1, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_inc(x_12);
x_13 = l___private_Init_Lean_Parser_Parser_8__updateTokens(x_12, x_2, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_8);
lean_inc(x_12);
x_16 = l_Lean_Parser_updateSyntaxNodeKinds(x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_31; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_8);
x_31 = lean_ctor_get(x_12, 2);
lean_inc(x_31);
lean_dec(x_12);
switch (lean_obj_tag(x_31)) {
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_32);
x_34 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_33);
x_35 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_7, x_34);
x_36 = lean_io_ref_set(x_1, x_35, x_16);
return x_36;
}
case 3:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_37);
x_39 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_38);
x_40 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(x_3, x_7, x_39);
x_41 = lean_io_ref_set(x_1, x_40, x_16);
return x_41;
}
default: 
{
lean_dec(x_31);
x_19 = x_8;
goto block_30;
}
}
block_30:
{
uint8_t x_20; 
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_7, 2, x_22);
x_23 = lean_io_ref_set(x_1, x_7, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_io_ref_set(x_1, x_28, x_16);
return x_29;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_53; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_42);
x_53 = lean_ctor_get(x_12, 2);
lean_inc(x_53);
lean_dec(x_12);
switch (lean_obj_tag(x_53)) {
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_54);
x_56 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_55);
x_57 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_7, x_56);
x_58 = lean_io_ref_set(x_1, x_57, x_43);
return x_58;
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_59);
x_61 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_60);
x_62 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(x_3, x_7, x_61);
x_63 = lean_io_ref_set(x_1, x_62, x_43);
return x_63;
}
default: 
{
lean_dec(x_53);
x_44 = x_8;
goto block_52;
}
}
block_52:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_48 = x_7;
} else {
 lean_dec_ref(x_7);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_47);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_io_ref_set(x_1, x_50, x_43);
return x_51;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
return x_16;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_13, 1);
lean_inc(x_68);
lean_dec(x_13);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_8);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_12);
x_70 = l_Lean_Parser_updateSyntaxNodeKinds(x_12, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_83; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_8);
lean_ctor_set(x_73, 1, x_71);
x_83 = lean_ctor_get(x_12, 2);
lean_inc(x_83);
lean_dec(x_12);
switch (lean_obj_tag(x_83)) {
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_84);
x_86 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_85);
x_87 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_7, x_86);
x_88 = lean_io_ref_set(x_1, x_87, x_73);
return x_88;
}
case 3:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_89);
x_91 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_90);
x_92 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(x_3, x_7, x_91);
x_93 = lean_io_ref_set(x_1, x_92, x_73);
return x_93;
}
default: 
{
lean_dec(x_83);
x_74 = x_8;
goto block_82;
}
}
block_82:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
x_75 = lean_ctor_get(x_7, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_7, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_7, 2);
lean_inc(x_77);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_78 = x_7;
} else {
 lean_dec_ref(x_7);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_3);
lean_ctor_set(x_79, 1, x_77);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 3, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_io_ref_set(x_1, x_80, x_73);
return x_81;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_94 = lean_ctor_get(x_70, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_96 = x_70;
} else {
 lean_dec_ref(x_70);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_13);
if (x_98 == 0)
{
return x_13;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_13, 0);
x_100 = lean_ctor_get(x_13, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_13);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_9, 1);
lean_inc(x_102);
lean_dec(x_9);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_8);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_ctor_get(x_3, 0);
lean_inc(x_104);
lean_inc(x_104);
x_105 = l___private_Init_Lean_Parser_Parser_8__updateTokens(x_104, x_2, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_8);
lean_ctor_set(x_108, 1, x_106);
lean_inc(x_104);
x_109 = l_Lean_Parser_updateSyntaxNodeKinds(x_104, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_122; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_8);
lean_ctor_set(x_112, 1, x_110);
x_122 = lean_ctor_get(x_104, 2);
lean_inc(x_122);
lean_dec(x_104);
switch (lean_obj_tag(x_122)) {
case 2:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_123);
x_125 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_124);
x_126 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_7, x_125);
x_127 = lean_io_ref_set(x_1, x_126, x_112);
return x_127;
}
case 3:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_122, 0);
lean_inc(x_128);
lean_dec(x_122);
x_129 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_128);
x_130 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_129);
x_131 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(x_3, x_7, x_130);
x_132 = lean_io_ref_set(x_1, x_131, x_112);
return x_132;
}
default: 
{
lean_dec(x_122);
x_113 = x_8;
goto block_121;
}
}
block_121:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_113);
x_114 = lean_ctor_get(x_7, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_7, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_7, 2);
lean_inc(x_116);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_117 = x_7;
} else {
 lean_dec_ref(x_7);
 x_117 = lean_box(0);
}
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_3);
lean_ctor_set(x_118, 1, x_116);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 3, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_118);
x_120 = lean_io_ref_set(x_1, x_119, x_112);
return x_120;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_3);
x_133 = lean_ctor_get(x_109, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_109, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_135 = x_109;
} else {
 lean_dec_ref(x_109);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_3);
x_137 = lean_ctor_get(x_105, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_105, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_139 = x_105;
} else {
 lean_dec_ref(x_105);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_9);
if (x_141 == 0)
{
return x_9;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_9, 0);
x_143 = lean_ctor_get(x_9, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_9);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_5, 0);
x_146 = lean_ctor_get(x_5, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_5);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_io_ref_reset(x_1, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_ctor_get(x_3, 0);
lean_inc(x_153);
lean_inc(x_153);
x_154 = l___private_Init_Lean_Parser_Parser_8__updateTokens(x_153, x_2, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_155);
lean_inc(x_153);
x_158 = l_Lean_Parser_updateSyntaxNodeKinds(x_153, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_171; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_147);
lean_ctor_set(x_161, 1, x_159);
x_171 = lean_ctor_get(x_153, 2);
lean_inc(x_171);
lean_dec(x_153);
switch (lean_obj_tag(x_171)) {
case 2:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_172);
x_174 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_173);
x_175 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__1(x_3, x_145, x_174);
x_176 = lean_io_ref_set(x_1, x_175, x_161);
return x_176;
}
case 3:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
lean_dec(x_171);
x_178 = l_List_map___main___at_Lean_Parser_addBuiltinLeadingParser___spec__1(x_177);
x_179 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_178);
x_180 = l_List_foldl___main___at_Lean_Parser_addBuiltinTrailingParser___spec__2(x_3, x_145, x_179);
x_181 = lean_io_ref_set(x_1, x_180, x_161);
return x_181;
}
default: 
{
lean_dec(x_171);
x_162 = x_147;
goto block_170;
}
}
block_170:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_162);
x_163 = lean_ctor_get(x_145, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_145, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_145, 2);
lean_inc(x_165);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 x_166 = x_145;
} else {
 lean_dec_ref(x_145);
 x_166 = lean_box(0);
}
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_3);
lean_ctor_set(x_167, 1, x_165);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 3, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_io_ref_set(x_1, x_168, x_161);
return x_169;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_3);
x_182 = lean_ctor_get(x_158, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_158, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_184 = x_158;
} else {
 lean_dec_ref(x_158);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_3);
x_186 = lean_ctor_get(x_154, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_154, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_188 = x_154;
} else {
 lean_dec_ref(x_154);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_145);
lean_dec(x_3);
lean_dec(x_2);
x_190 = lean_ctor_get(x_149, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_149, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_192 = x_149;
} else {
 lean_dec_ref(x_149);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_3);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_5);
if (x_194 == 0)
{
return x_5;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_5, 0);
x_196 = lean_ctor_get(x_5, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_5);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_addBuiltinTrailingParser(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
lean_inc(x_4);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_4);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
lean_inc(x_10);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_declareBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_InitAttr_1__getIOTypeArg___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_InitAttr_2__isUnitType___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_2 = l_Lean_Parser_declareBuiltinParser___closed__4;
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareBuiltinParser___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin parser '");
return x_1;
}
}
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = l_Lean_Parser_declareBuiltinParser___closed__2;
lean_inc(x_4);
x_7 = l_Lean_Name_append___main(x_6, x_4);
x_8 = lean_box(0);
x_9 = lean_expr_mk_const(x_3, x_8);
lean_inc(x_4);
x_10 = l_Lean_nameToExprAux___main(x_4);
lean_inc(x_4);
x_11 = lean_expr_mk_const(x_4, x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_mkCApp(x_2, x_14);
x_16 = l_Lean_Parser_declareBuiltinParser___closed__5;
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_box(0);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Options_empty;
x_23 = l_Lean_Environment_addAndCompile(x_1, x_22, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_23);
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_4);
x_28 = l_Lean_Parser_declareBuiltinParser___closed__6;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_dec(x_5);
x_33 = l_System_FilePath_dirName___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_4);
x_35 = l_Lean_Parser_declareBuiltinParser___closed__6;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_40 = lean_ctor_get(x_23, 0);
lean_inc(x_40);
lean_dec(x_23);
x_41 = l_Lean_initAttr;
x_42 = lean_box(0);
x_43 = l_Lean_ParametricAttribute_setParam___rarg(x_41, x_40, x_7, x_42);
x_44 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_43, x_5);
lean_dec(x_43);
return x_44;
}
}
}
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_Syntax_formatStx___main___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinLeadingParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_declareLeadingBuiltinParser___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_declareLeadingBuiltinParser___closed__3;
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTrailingParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_declareTrailingBuiltinParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_declareTrailingBuiltinParser___closed__2;
x_6 = l_Lean_Parser_declareBuiltinParser(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parser type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' (`Parser` or `TrailingParser` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Syntax_formatStx___main___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ParserKind");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leading");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__7;
x_2 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Syntax_isMissing___rarg(x_5);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = l_System_FilePath_dirName___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_1);
x_13 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_registerTagAttribute___lambda__4___closed__2;
x_16 = lean_string_append(x_14, x_15);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_System_FilePath_dirName___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_registerTagAttribute___lambda__4___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
else
{
if (x_6 == 0)
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_7, 0);
lean_dec(x_26);
x_27 = l_System_FilePath_dirName___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_registerTagAttribute___lambda__4___closed__3;
x_32 = lean_string_append(x_30, x_31);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_32);
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_dec(x_7);
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_1);
x_36 = l_Lean_registerTagAttribute___lambda__4___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_registerTagAttribute___lambda__4___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_42 = x_7;
} else {
 lean_dec_ref(x_7);
 x_42 = lean_box(0);
}
x_52 = lean_box(0);
lean_inc(x_41);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_41);
lean_inc(x_4);
lean_inc(x_3);
x_54 = lean_environment_find(x_3, x_4);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_41);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_ConstantInfo_type(x_57);
lean_dec(x_57);
switch (lean_obj_tag(x_58)) {
case 4:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4;
x_61 = lean_name_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_2);
x_43 = x_52;
goto block_51;
}
else
{
lean_object* x_62; 
lean_dec(x_42);
lean_dec(x_41);
x_62 = l_Lean_Parser_declareTrailingBuiltinParser(x_3, x_2, x_4, x_53);
return x_62;
}
}
case 5:
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 4)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5;
x_67 = lean_name_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_2);
x_43 = x_52;
goto block_51;
}
else
{
if (lean_obj_tag(x_64) == 4)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_69 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__9;
x_70 = lean_name_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_2);
x_43 = x_52;
goto block_51;
}
else
{
lean_object* x_71; 
lean_dec(x_42);
lean_dec(x_41);
x_71 = l_Lean_Parser_declareLeadingBuiltinParser(x_3, x_2, x_4, x_53);
return x_71;
}
}
else
{
lean_dec(x_64);
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_2);
x_43 = x_52;
goto block_51;
}
}
}
else
{
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_2);
x_43 = x_52;
goto block_51;
}
}
default: 
{
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_3);
lean_dec(x_2);
x_43 = x_52;
goto block_51;
}
}
}
block_51:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_44 = l_System_FilePath_dirName___closed__1;
x_45 = l_Lean_Name_toStringWithSep___main(x_44, x_4);
x_46 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2;
x_49 = lean_string_append(x_47, x_48);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_42;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin parser");
return x_1;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed), 7, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
x_8 = l_Lean_AttributeImpl_inhabited___closed__4;
x_9 = l_Lean_AttributeImpl_inhabited___closed__5;
x_10 = 1;
x_11 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set(x_11, 4, x_6);
lean_ctor_set(x_11, 5, x_8);
lean_ctor_set(x_11, 6, x_9);
lean_ctor_set(x_11, 7, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*8, x_10);
x_12 = l_Lean_registerAttribute(x_11, x_3);
return x_12;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Parser_registerBuiltinParserAttribute___lambda__1(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_5);
return x_9;
}
}
lean_object* _init_l_Lean_Parser_runBuiltinParserUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access builtin reference");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_runBuiltinParserUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_runBuiltinParserUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Parser_runBuiltinParserUnsafe___closed__2;
x_12 = lean_io_ref_get(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_5);
x_14 = l_Lean_Parser_prattParser(x_1, x_13, x_3, x_4, x_5);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_6 = x_15;
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_6 = x_17;
goto block_10;
}
block_10:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = l_Lean_Parser_runBuiltinParserUnsafe___closed__1;
x_8 = l_Lean_Parser_ParserState_mkError(x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
}
lean_object* l_Lean_Parser_runBuiltinParserUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_runBuiltinParserUnsafe(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_runBuiltinParser___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_runBuiltinParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_runBuiltinParser___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_Lean_Parser_runBuiltinParser___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_runBuiltinParser___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_runBuiltinParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_runBuiltinParser(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Parser_ParserAttribute_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Parser_ParsingTables_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Parser_ParserAttribute_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Parser_ParserAttribute_inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_ParserAttribute_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Parser_ParserAttribute_inhabited___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Parser_ParserAttribute_inhabited___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_Parser_ParserAttribute_inhabited___closed__3;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Parser_ParserAttribute_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_ParserAttribute_inhabited___closed__4;
return x_1;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 0, x_14);
x_15 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_16 = lean_io_ref_get(x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_16, 0, x_14);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = l_Lean_Parser_ParserAttribute_inhabited___closed__1;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_io_ref_get(x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_14);
x_25 = lean_io_ref_reset(x_15, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_29 = x_21;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_15, x_30, x_25);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_43 = x_21;
x_44 = lean_array_push(x_24, x_43);
x_45 = lean_io_ref_set(x_15, x_44, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_21);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_dec(x_21);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_io_ref_reset(x_15, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_21);
x_65 = x_21;
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_io_ref_set(x_15, x_66, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_21);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
lean_dec(x_21);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_77 = x_60;
} else {
 lean_dec_ref(x_60);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_21);
x_79 = !lean_is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_22, 0);
x_81 = lean_ctor_get(x_22, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_22);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = lean_ctor_get(x_16, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_16);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_14);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_get_size(x_83);
lean_dec(x_83);
x_87 = l_Lean_Parser_ParserAttribute_inhabited___closed__1;
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_1);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_io_ref_get(x_15, x_85);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_14);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_io_ref_reset(x_15, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_14);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_88);
x_99 = x_88;
x_100 = lean_array_push(x_90, x_99);
x_101 = lean_io_ref_set(x_15, x_100, x_97);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_88);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_107 = x_101;
} else {
 lean_dec_ref(x_101);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_88);
x_109 = lean_ctor_get(x_94, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_94, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_111 = x_94;
} else {
 lean_dec_ref(x_94);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_88);
x_113 = lean_ctor_get(x_89, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_89, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_115 = x_89;
} else {
 lean_dec_ref(x_89);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_16, 0);
x_119 = lean_ctor_get(x_16, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_16);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
lean_dec(x_3);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_125 = lean_io_ref_get(x_124, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_array_get_size(x_126);
lean_dec(x_126);
x_131 = l_Lean_Parser_ParserAttribute_inhabited___closed__1;
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_1);
lean_ctor_set(x_132, 2, x_131);
x_133 = lean_io_ref_get(x_124, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_io_ref_reset(x_124, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_122);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_132);
x_143 = x_132;
x_144 = lean_array_push(x_134, x_143);
x_145 = lean_io_ref_set(x_124, x_144, x_141);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_132);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_132);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_134);
lean_dec(x_132);
x_153 = lean_ctor_get(x_138, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_155 = x_138;
} else {
 lean_dec_ref(x_138);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_132);
x_157 = lean_ctor_get(x_133, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_133, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_159 = x_133;
} else {
 lean_dec_ref(x_133);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_125, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_125, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_163 = x_125;
} else {
 lean_dec_ref(x_125);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_3, 0);
x_167 = lean_ctor_get(x_3, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_3);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2(x_1, x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Array_empty___closed__1;
lean_inc(x_10);
x_12 = lean_apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__3(x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_9);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_io_ref_get(x_3, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_9);
x_26 = lean_io_ref_reset(x_3, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_9);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_30 = x_22;
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_26);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_22);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_44 = x_22;
x_45 = lean_array_push(x_25, x_44);
x_46 = lean_io_ref_set(x_3, x_45, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_22);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_25);
lean_dec(x_22);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_26, 0);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_26);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_9);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_io_ref_reset(x_3, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_9);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_66 = x_22;
x_67 = lean_array_push(x_58, x_66);
x_68 = lean_io_ref_set(x_3, x_67, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_22);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_22);
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_78 = x_61;
} else {
 lean_dec_ref(x_61);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_22);
x_80 = !lean_is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_23, 0);
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_23);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_9);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 4);
lean_inc(x_90);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_10);
lean_ctor_set(x_91, 3, x_88);
lean_ctor_set(x_91, 4, x_89);
lean_ctor_set(x_91, 5, x_90);
x_92 = lean_io_ref_get(x_3, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_9);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_io_ref_reset(x_3, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_9);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_91);
x_102 = x_91;
x_103 = lean_array_push(x_93, x_102);
x_104 = lean_io_ref_set(x_3, x_103, x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_91);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_91);
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_114 = x_97;
} else {
 lean_dec_ref(x_97);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
x_116 = lean_ctor_get(x_92, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_118 = x_92;
} else {
 lean_dec_ref(x_92);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_10);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_15);
if (x_120 == 0)
{
return x_15;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_15, 0);
x_122 = lean_ctor_get(x_15, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_15);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
lean_dec(x_1);
x_125 = l_System_FilePath_dirName___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean_string_append(x_127, x_126);
lean_dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean_string_append(x_128, x_129);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_130);
return x_4;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_4, 0);
x_132 = lean_ctor_get(x_4, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_4);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2(x_1, x_131, x_133);
lean_dec(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
x_138 = l_Array_empty___closed__1;
lean_inc(x_137);
x_139 = lean_apply_1(x_137, x_138);
x_140 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_141 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_141, 0, x_139);
lean_closure_set(x_141, 1, x_140);
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__3(x_141, x_136);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_1, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_1, 4);
lean_inc(x_150);
lean_dec(x_1);
x_151 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_147);
lean_ctor_set(x_151, 2, x_137);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set(x_151, 4, x_149);
lean_ctor_set(x_151, 5, x_150);
x_152 = lean_io_ref_get(x_3, x_146);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_135);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_io_ref_reset(x_3, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_135);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_151);
x_162 = x_151;
x_163 = lean_array_push(x_153, x_162);
x_164 = lean_io_ref_set(x_3, x_163, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_151);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_151);
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_170 = x_164;
} else {
 lean_dec_ref(x_164);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_153);
lean_dec(x_151);
x_172 = lean_ctor_get(x_157, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_157, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_174 = x_157;
} else {
 lean_dec_ref(x_157);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_151);
x_176 = lean_ctor_get(x_152, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_152, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_178 = x_152;
} else {
 lean_dec_ref(x_152);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_137);
lean_dec(x_1);
x_180 = lean_ctor_get(x_142, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_142, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_182 = x_142;
} else {
 lean_dec_ref(x_142);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_1, 0);
lean_inc(x_184);
lean_dec(x_1);
x_185 = l_System_FilePath_dirName___closed__1;
x_186 = l_Lean_Name_toStringWithSep___main(x_185, x_184);
x_187 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_188 = lean_string_append(x_187, x_186);
lean_dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean_string_append(x_188, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_132);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_4);
if (x_192 == 0)
{
return x_4;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_4, 0);
x_194 = lean_ctor_get(x_4, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_4);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
lean_object* l_Lean_Parser_registerParserAttribute___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = l_Lean_Parser_ParsingTables_inhabited___closed__1;
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Parser_ParsingTables_inhabited___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_io_ref_get(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* _init_l_Lean_Parser_registerParserAttribute___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parser attribute");
return x_1;
}
}
lean_object* _init_l_Lean_Parser_registerParserAttribute___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_registerParserAttribute___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_registerParserAttribute___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_registerParserAttribute___lambda__2___closed__2;
return x_2;
}
}
lean_object* _init_l_Lean_Parser_registerParserAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_registerParserAttribute___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_registerParserAttribute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_registerParserAttribute___lambda__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_9 = l_Lean_Parser_registerParserAttribute___closed__1;
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_9);
x_11 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Parser_registerParserAttribute___spec__1(x_10, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_15, 0, x_1);
x_16 = l_Lean_AttributeImpl_inhabited___closed__1;
x_17 = l_Lean_AttributeImpl_inhabited___closed__4;
x_18 = l_Lean_AttributeImpl_inhabited___closed__5;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_17);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*8, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_24, 0, x_1);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = l_Lean_AttributeImpl_inhabited___closed__1;
x_27 = l_Lean_AttributeImpl_inhabited___closed__4;
x_28 = l_Lean_AttributeImpl_inhabited___closed__5;
x_29 = 0;
x_30 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_29);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_Parser_registerParserAttribute___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_registerParserAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_registerParserAttribute___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_registerParserAttribute___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_registerParserAttribute___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserAttribute_runParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Parser_prattParser(x_8, x_7, x_2, x_3, x_4);
return x_9;
}
}
uint8_t l_Lean_Syntax_isNone___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_nullKind;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
lean_object* l_Lean_Syntax_isNone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isNone___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNone___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isNone___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getOptional___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_nullKind;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_3, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_getOptional(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getOptional___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptional___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptionalIdent___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_Syntax_getId___rarg(x_5);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Syntax_getOptionalIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getOptionalIdent___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptionalIdent___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptionalIdent___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_nat_add(x_1, x_2);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___rarg(x_3, x_2, x_4, x_5, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_4);
x_14 = lean_apply_2(x_4, x_12, x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___rarg), 6, 0);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mfoldArgsAux___main(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___rarg), 6, 0);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mfoldArgsAux(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Syntax_getArgs___rarg(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___rarg(x_1, x_6, x_5, x_3, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_Syntax_mfoldArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgs___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mfoldArgs___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_mfoldArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mfoldArgs(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_5);
x_10 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_10;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Syntax_getArgs___rarg(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg(x_2, x_5, x_4, x_6, x_3);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Syntax_foldArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldArgs___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Syntax_foldArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgs___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_nat_add(x_1, x_2);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg(x_3, x_4, x_2, x_5, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_4);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_mforArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Syntax_getArgs___rarg(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg(x_1, x_3, x_5, x_4, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Syntax_mforArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_mforArgs___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforArgs___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mforArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mforArgs___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_mforArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mforArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mfoldSepArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Syntax_getArgs___rarg(x_2);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___rarg(x_1, x_6, x_5, x_3, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_Syntax_mfoldSepArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldSepArgs___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldSepArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mfoldSepArgs___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_mfoldSepArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mfoldSepArgs(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_5);
x_10 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_10;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_foldSepArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Syntax_getArgs___rarg(x_1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg(x_2, x_5, x_4, x_6, x_3);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Syntax_foldSepArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_foldSepArgs___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_foldSepArgs___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Syntax_foldSepArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldSepArgs___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_nat_add(x_1, x_2);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg(x_3, x_4, x_2, x_5, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_4);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_mforSepArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Syntax_getArgs___rarg(x_2);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg(x_1, x_3, x_5, x_4, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Syntax_mforSepArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_mforSepArgs___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Syntax_mforSepArgs___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_mforSepArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mforSepArgs___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_mforSepArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mforSepArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Lean_Position(lean_object*);
lean_object* initialize_Init_Lean_Syntax(lean_object*);
lean_object* initialize_Init_Lean_ToExpr(lean_object*);
lean_object* initialize_Init_Lean_Message(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Attributes(lean_object*);
lean_object* initialize_Init_Lean_Parser_Trie(lean_object*);
lean_object* initialize_Init_Lean_Parser_Identifier(lean_object*);
lean_object* initialize_Init_Lean_Compiler_InitAttr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Parser(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Position(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Syntax(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_ToExpr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Message(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Environment(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Attributes(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Trie(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Identifier(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_InitAttr(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Parser_appPrec = _init_l_Lean_Parser_appPrec();
lean_mark_persistent(l_Lean_Parser_appPrec);
l_Lean_Parser_TokenConfig_HasBeq___closed__1 = _init_l_Lean_Parser_TokenConfig_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Parser_TokenConfig_HasBeq___closed__1);
l_Lean_Parser_TokenConfig_HasBeq = _init_l_Lean_Parser_TokenConfig_HasBeq();
lean_mark_persistent(l_Lean_Parser_TokenConfig_HasBeq);
l_Lean_Parser_TokenConfig_toStr___closed__1 = _init_l_Lean_Parser_TokenConfig_toStr___closed__1();
lean_mark_persistent(l_Lean_Parser_TokenConfig_toStr___closed__1);
l_Lean_Parser_TokenConfig_HasToString___closed__1 = _init_l_Lean_Parser_TokenConfig_HasToString___closed__1();
lean_mark_persistent(l_Lean_Parser_TokenConfig_HasToString___closed__1);
l_Lean_Parser_TokenConfig_HasToString = _init_l_Lean_Parser_TokenConfig_HasToString();
lean_mark_persistent(l_Lean_Parser_TokenConfig_HasToString);
l_Lean_Parser_ParserContextCore_inhabited___closed__1 = _init_l_Lean_Parser_ParserContextCore_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserContextCore_inhabited___closed__1);
l_Lean_Parser_ParserContextCore_inhabited = _init_l_Lean_Parser_ParserContextCore_inhabited();
lean_mark_persistent(l_Lean_Parser_ParserContextCore_inhabited);
l_Lean_Parser_Error_Inhabited___closed__1 = _init_l_Lean_Parser_Error_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_Inhabited___closed__1);
l_Lean_Parser_Error_Inhabited = _init_l_Lean_Parser_Error_Inhabited();
lean_mark_persistent(l_Lean_Parser_Error_Inhabited);
l___private_Init_Lean_Parser_Parser_1__expectedToString___main___closed__1 = _init_l___private_Init_Lean_Parser_Parser_1__expectedToString___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Parser_Parser_1__expectedToString___main___closed__1);
l_Lean_Parser_Error_toString___closed__1 = _init_l_Lean_Parser_Error_toString___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__1);
l_Lean_Parser_Error_toString___closed__2 = _init_l_Lean_Parser_Error_toString___closed__2();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__2);
l_Lean_Parser_Error_toString___closed__3 = _init_l_Lean_Parser_Error_toString___closed__3();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__3);
l_Lean_Parser_Error_toString___closed__4 = _init_l_Lean_Parser_Error_toString___closed__4();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__4);
l_Lean_Parser_Error_HasToString___closed__1 = _init_l_Lean_Parser_Error_HasToString___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_HasToString___closed__1);
l_Lean_Parser_Error_HasToString = _init_l_Lean_Parser_Error_HasToString();
lean_mark_persistent(l_Lean_Parser_Error_HasToString);
l_Lean_Parser_Error_HasBeq___closed__1 = _init_l_Lean_Parser_Error_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_HasBeq___closed__1);
l_Lean_Parser_Error_HasBeq = _init_l_Lean_Parser_Error_HasBeq();
lean_mark_persistent(l_Lean_Parser_Error_HasBeq);
l_Lean_Parser_ParserState_mkEOIError___closed__1 = _init_l_Lean_Parser_ParserState_mkEOIError___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_mkEOIError___closed__1);
l_Lean_Parser_FirstTokens_toStr___closed__1 = _init_l_Lean_Parser_FirstTokens_toStr___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__1);
l_Lean_Parser_FirstTokens_toStr___closed__2 = _init_l_Lean_Parser_FirstTokens_toStr___closed__2();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__2);
l_Lean_Parser_FirstTokens_toStr___closed__3 = _init_l_Lean_Parser_FirstTokens_toStr___closed__3();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__3);
l_Lean_Parser_FirstTokens_HasToString___closed__1 = _init_l_Lean_Parser_FirstTokens_HasToString___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_HasToString___closed__1);
l_Lean_Parser_FirstTokens_HasToString = _init_l_Lean_Parser_FirstTokens_HasToString();
lean_mark_persistent(l_Lean_Parser_FirstTokens_HasToString);
l_Lean_Parser_Parser_inhabited___closed__1 = _init_l_Lean_Parser_Parser_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_Parser_inhabited___closed__1);
l_Lean_Parser_Parser_inhabited___closed__2 = _init_l_Lean_Parser_Parser_inhabited___closed__2();
lean_mark_persistent(l_Lean_Parser_Parser_inhabited___closed__2);
l_Lean_Parser_epsilonInfo___closed__1 = _init_l_Lean_Parser_epsilonInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__1);
l_Lean_Parser_epsilonInfo___closed__2 = _init_l_Lean_Parser_epsilonInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__2);
l_Lean_Parser_epsilonInfo___closed__3 = _init_l_Lean_Parser_epsilonInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__3);
l_Lean_Parser_epsilonInfo = _init_l_Lean_Parser_epsilonInfo();
lean_mark_persistent(l_Lean_Parser_epsilonInfo);
l_Lean_Parser_pushLeading___closed__1 = _init_l_Lean_Parser_pushLeading___closed__1();
lean_mark_persistent(l_Lean_Parser_pushLeading___closed__1);
l_Lean_Parser_pushLeading___closed__2 = _init_l_Lean_Parser_pushLeading___closed__2();
lean_mark_persistent(l_Lean_Parser_pushLeading___closed__2);
l_Lean_Parser_pushLeading = _init_l_Lean_Parser_pushLeading();
lean_mark_persistent(l_Lean_Parser_pushLeading);
l_Lean_Parser_checkLeadingFn___closed__1 = _init_l_Lean_Parser_checkLeadingFn___closed__1();
lean_mark_persistent(l_Lean_Parser_checkLeadingFn___closed__1);
l_Lean_Parser_manyAux___main___closed__1 = _init_l_Lean_Parser_manyAux___main___closed__1();
lean_mark_persistent(l_Lean_Parser_manyAux___main___closed__1);
l_Lean_Parser_hexDigitFn___closed__1 = _init_l_Lean_Parser_hexDigitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_hexDigitFn___closed__1);
l_Lean_Parser_quotedCharFn___closed__1 = _init_l_Lean_Parser_quotedCharFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharFn___closed__1);
l_Lean_Parser_charLitFnAux___closed__1 = _init_l_Lean_Parser_charLitFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFnAux___closed__1);
l_Lean_Parser_binNumberFn___closed__1 = _init_l_Lean_Parser_binNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_binNumberFn___closed__1);
l_Lean_Parser_octalNumberFn___closed__1 = _init_l_Lean_Parser_octalNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_octalNumberFn___closed__1);
l_Lean_Parser_hexNumberFn___closed__1 = _init_l_Lean_Parser_hexNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_hexNumberFn___closed__1);
l_Lean_Parser_numberFnAux___closed__1 = _init_l_Lean_Parser_numberFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_numberFnAux___closed__1);
l_Lean_Parser_mkTokenAndFixPos___closed__1 = _init_l_Lean_Parser_mkTokenAndFixPos___closed__1();
lean_mark_persistent(l_Lean_Parser_mkTokenAndFixPos___closed__1);
l_Lean_Parser_identFnAux___main___closed__1 = _init_l_Lean_Parser_identFnAux___main___closed__1();
lean_mark_persistent(l_Lean_Parser_identFnAux___main___closed__1);
l_Lean_Parser_insertToken___closed__1 = _init_l_Lean_Parser_insertToken___closed__1();
lean_mark_persistent(l_Lean_Parser_insertToken___closed__1);
l_Lean_Parser_insertToken___closed__2 = _init_l_Lean_Parser_insertToken___closed__2();
lean_mark_persistent(l_Lean_Parser_insertToken___closed__2);
l_Lean_Parser_insertToken___closed__3 = _init_l_Lean_Parser_insertToken___closed__3();
lean_mark_persistent(l_Lean_Parser_insertToken___closed__3);
l_Lean_Parser_insertToken___closed__4 = _init_l_Lean_Parser_insertToken___closed__4();
lean_mark_persistent(l_Lean_Parser_insertToken___closed__4);
l_Lean_Parser_insertToken___closed__5 = _init_l_Lean_Parser_insertToken___closed__5();
lean_mark_persistent(l_Lean_Parser_insertToken___closed__5);
l_Lean_Parser_symbolInfo___closed__1 = _init_l_Lean_Parser_symbolInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_symbolInfo___closed__1);
l_Lean_Parser_symbolOrIdentInfo___closed__1 = _init_l_Lean_Parser_symbolOrIdentInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_symbolOrIdentInfo___closed__1);
l_Lean_Parser_symbolOrIdentInfo___closed__2 = _init_l_Lean_Parser_symbolOrIdentInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_symbolOrIdentInfo___closed__2);
l_Lean_Parser_symbolOrIdentInfo___closed__3 = _init_l_Lean_Parser_symbolOrIdentInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_symbolOrIdentInfo___closed__3);
l_Lean_Parser_symbolOrIdentInfo___closed__4 = _init_l_Lean_Parser_symbolOrIdentInfo___closed__4();
lean_mark_persistent(l_Lean_Parser_symbolOrIdentInfo___closed__4);
l_Lean_Parser_symbolOrIdentInfo___closed__5 = _init_l_Lean_Parser_symbolOrIdentInfo___closed__5();
lean_mark_persistent(l_Lean_Parser_symbolOrIdentInfo___closed__5);
l_Lean_Parser_insertNoWsToken___closed__1 = _init_l_Lean_Parser_insertNoWsToken___closed__1();
lean_mark_persistent(l_Lean_Parser_insertNoWsToken___closed__1);
l_Lean_Parser_symbolNoWsInfo___closed__1 = _init_l_Lean_Parser_symbolNoWsInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_symbolNoWsInfo___closed__1);
l_Lean_Parser_symbolNoWsFn___closed__1 = _init_l_Lean_Parser_symbolNoWsFn___closed__1();
lean_mark_persistent(l_Lean_Parser_symbolNoWsFn___closed__1);
l_Lean_Parser_unicodeSymbolInfo___closed__1 = _init_l_Lean_Parser_unicodeSymbolInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolInfo___closed__1);
l_Lean_Parser_unicodeSymbolFn___rarg___closed__1 = _init_l_Lean_Parser_unicodeSymbolFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolFn___rarg___closed__1);
l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1 = _init_l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__1);
l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2 = _init_l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolCheckPrecFn___closed__2);
l_Lean_Parser_mkAtomicInfo___closed__1 = _init_l_Lean_Parser_mkAtomicInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__1);
l_Lean_Parser_mkAtomicInfo___closed__2 = _init_l_Lean_Parser_mkAtomicInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__2);
l_Lean_Parser_numLit___closed__1 = _init_l_Lean_Parser_numLit___closed__1();
lean_mark_persistent(l_Lean_Parser_numLit___closed__1);
l_Lean_Parser_strLitFn___rarg___closed__1 = _init_l_Lean_Parser_strLitFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitFn___rarg___closed__1);
l_Lean_Parser_strLit___closed__1 = _init_l_Lean_Parser_strLit___closed__1();
lean_mark_persistent(l_Lean_Parser_strLit___closed__1);
l_Lean_Parser_charLitFn___rarg___closed__1 = _init_l_Lean_Parser_charLitFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFn___rarg___closed__1);
l_Lean_Parser_charLit___closed__1 = _init_l_Lean_Parser_charLit___closed__1();
lean_mark_persistent(l_Lean_Parser_charLit___closed__1);
l_Lean_Parser_identFn___rarg___closed__1 = _init_l_Lean_Parser_identFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_identFn___rarg___closed__1);
l_Lean_Parser_ident___closed__1 = _init_l_Lean_Parser_ident___closed__1();
lean_mark_persistent(l_Lean_Parser_ident___closed__1);
l_Lean_Parser_rawIdent___closed__1 = _init_l_Lean_Parser_rawIdent___closed__1();
lean_mark_persistent(l_Lean_Parser_rawIdent___closed__1);
l_Lean_Parser_quotedSymbolFn___rarg___closed__1 = _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedSymbolFn___rarg___closed__1);
l_Lean_Parser_quotedSymbolFn___rarg___closed__2 = _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_quotedSymbolFn___rarg___closed__2);
l_Lean_Parser_quotedSymbolFn___rarg___closed__3 = _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__3();
lean_mark_persistent(l_Lean_Parser_quotedSymbolFn___rarg___closed__3);
l_Lean_Parser_quotedSymbolFn___rarg___closed__4 = _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__4();
lean_mark_persistent(l_Lean_Parser_quotedSymbolFn___rarg___closed__4);
l_Lean_Parser_quotedSymbolFn___rarg___closed__5 = _init_l_Lean_Parser_quotedSymbolFn___rarg___closed__5();
lean_mark_persistent(l_Lean_Parser_quotedSymbolFn___rarg___closed__5);
l_Lean_Parser_unquotedSymbolFn___rarg___closed__1 = _init_l_Lean_Parser_unquotedSymbolFn___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_unquotedSymbolFn___rarg___closed__1);
l_Lean_Parser_fieldIdxFn___closed__1 = _init_l_Lean_Parser_fieldIdxFn___closed__1();
lean_mark_persistent(l_Lean_Parser_fieldIdxFn___closed__1);
l_Lean_Parser_fieldIdx___closed__1 = _init_l_Lean_Parser_fieldIdx___closed__1();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__1);
l_Lean_Parser_fieldIdx___closed__2 = _init_l_Lean_Parser_fieldIdx___closed__2();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__2);
l_Lean_Parser_longestMatchFn___closed__1 = _init_l_Lean_Parser_longestMatchFn___closed__1();
lean_mark_persistent(l_Lean_Parser_longestMatchFn___closed__1);
l_Lean_Parser_anyOfFn___main___closed__1 = _init_l_Lean_Parser_anyOfFn___main___closed__1();
lean_mark_persistent(l_Lean_Parser_anyOfFn___main___closed__1);
l_Lean_Parser_ParsingTables_inhabited___closed__1 = _init_l_Lean_Parser_ParsingTables_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_ParsingTables_inhabited___closed__1);
l_Lean_Parser_ParsingTables_inhabited = _init_l_Lean_Parser_ParsingTables_inhabited();
lean_mark_persistent(l_Lean_Parser_ParsingTables_inhabited);
l_Lean_Parser_indexed___rarg___closed__1 = _init_l_Lean_Parser_indexed___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_indexed___rarg___closed__1);
w = l_Lean_Parser_mkBuiltinTokenTable(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
l_Lean_Parser_TokenTableAttribute_inhabited___closed__1 = _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_TokenTableAttribute_inhabited___closed__1);
l_Lean_Parser_TokenTableAttribute_inhabited___closed__2 = _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__2();
lean_mark_persistent(l_Lean_Parser_TokenTableAttribute_inhabited___closed__2);
l_Lean_Parser_TokenTableAttribute_inhabited___closed__3 = _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__3();
lean_mark_persistent(l_Lean_Parser_TokenTableAttribute_inhabited___closed__3);
l_Lean_Parser_TokenTableAttribute_inhabited___closed__4 = _init_l_Lean_Parser_TokenTableAttribute_inhabited___closed__4();
lean_mark_persistent(l_Lean_Parser_TokenTableAttribute_inhabited___closed__4);
l_Lean_Parser_TokenTableAttribute_inhabited = _init_l_Lean_Parser_TokenTableAttribute_inhabited();
lean_mark_persistent(l_Lean_Parser_TokenTableAttribute_inhabited);
w = l_Lean_Parser_mkTokenTableAttribute(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Parser_tokenTableAttribute = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_Parser_tokenTableAttribute);
l_Lean_Parser_mkSyntaxNodeKindSetRef___closed__1 = _init_l_Lean_Parser_mkSyntaxNodeKindSetRef___closed__1();
lean_mark_persistent(l_Lean_Parser_mkSyntaxNodeKindSetRef___closed__1);
w = l_Lean_Parser_mkSyntaxNodeKindSetRef(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Parser_syntaxNodeKindSetRef = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_Parser_syntaxNodeKindSetRef);
l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1 = _init_l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1();
lean_mark_persistent(l___private_Init_Lean_Parser_Parser_8__updateTokens___closed__1);
l_Lean_Parser_addBuiltinLeadingParser___closed__1 = _init_l_Lean_Parser_addBuiltinLeadingParser___closed__1();
lean_mark_persistent(l_Lean_Parser_addBuiltinLeadingParser___closed__1);
l_Lean_Parser_declareBuiltinParser___closed__1 = _init_l_Lean_Parser_declareBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__1);
l_Lean_Parser_declareBuiltinParser___closed__2 = _init_l_Lean_Parser_declareBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__2);
l_Lean_Parser_declareBuiltinParser___closed__3 = _init_l_Lean_Parser_declareBuiltinParser___closed__3();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__3);
l_Lean_Parser_declareBuiltinParser___closed__4 = _init_l_Lean_Parser_declareBuiltinParser___closed__4();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__4);
l_Lean_Parser_declareBuiltinParser___closed__5 = _init_l_Lean_Parser_declareBuiltinParser___closed__5();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__5);
l_Lean_Parser_declareBuiltinParser___closed__6 = _init_l_Lean_Parser_declareBuiltinParser___closed__6();
lean_mark_persistent(l_Lean_Parser_declareBuiltinParser___closed__6);
l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__1);
l_Lean_Parser_declareLeadingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__2);
l_Lean_Parser_declareLeadingBuiltinParser___closed__3 = _init_l_Lean_Parser_declareLeadingBuiltinParser___closed__3();
lean_mark_persistent(l_Lean_Parser_declareLeadingBuiltinParser___closed__3);
l_Lean_Parser_declareTrailingBuiltinParser___closed__1 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__1();
lean_mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__1);
l_Lean_Parser_declareTrailingBuiltinParser___closed__2 = _init_l_Lean_Parser_declareTrailingBuiltinParser___closed__2();
lean_mark_persistent(l_Lean_Parser_declareTrailingBuiltinParser___closed__2);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__1);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__2);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__3);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__4);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__5);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__6);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__7 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__7);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__8 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__8);
l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__9 = _init_l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___lambda__1___closed__9);
l_Lean_Parser_registerBuiltinParserAttribute___closed__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
l_Lean_Parser_runBuiltinParserUnsafe___closed__1 = _init_l_Lean_Parser_runBuiltinParserUnsafe___closed__1();
lean_mark_persistent(l_Lean_Parser_runBuiltinParserUnsafe___closed__1);
l_Lean_Parser_runBuiltinParserUnsafe___closed__2 = _init_l_Lean_Parser_runBuiltinParserUnsafe___closed__2();
lean_mark_persistent(l_Lean_Parser_runBuiltinParserUnsafe___closed__2);
l_Lean_Parser_ParserAttribute_inhabited___closed__1 = _init_l_Lean_Parser_ParserAttribute_inhabited___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserAttribute_inhabited___closed__1);
l_Lean_Parser_ParserAttribute_inhabited___closed__2 = _init_l_Lean_Parser_ParserAttribute_inhabited___closed__2();
lean_mark_persistent(l_Lean_Parser_ParserAttribute_inhabited___closed__2);
l_Lean_Parser_ParserAttribute_inhabited___closed__3 = _init_l_Lean_Parser_ParserAttribute_inhabited___closed__3();
lean_mark_persistent(l_Lean_Parser_ParserAttribute_inhabited___closed__3);
l_Lean_Parser_ParserAttribute_inhabited___closed__4 = _init_l_Lean_Parser_ParserAttribute_inhabited___closed__4();
lean_mark_persistent(l_Lean_Parser_ParserAttribute_inhabited___closed__4);
l_Lean_Parser_ParserAttribute_inhabited = _init_l_Lean_Parser_ParserAttribute_inhabited();
lean_mark_persistent(l_Lean_Parser_ParserAttribute_inhabited);
l_Lean_Parser_registerParserAttribute___lambda__2___closed__1 = _init_l_Lean_Parser_registerParserAttribute___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_registerParserAttribute___lambda__2___closed__1);
l_Lean_Parser_registerParserAttribute___lambda__2___closed__2 = _init_l_Lean_Parser_registerParserAttribute___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_registerParserAttribute___lambda__2___closed__2);
l_Lean_Parser_registerParserAttribute___closed__1 = _init_l_Lean_Parser_registerParserAttribute___closed__1();
lean_mark_persistent(l_Lean_Parser_registerParserAttribute___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
