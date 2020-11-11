// Lean compiler output
// Module: Lean.PrettyPrinter.Formatter
// Imports: Init Lean.CoreM Lean.Parser.Extension Lean.KeyedDeclsAttribute Lean.ParserCompiler.Attribute Lean.PrettyPrinter.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_State_stack___default;
extern lean_object* l_Lean_Parser_builtinTokenTable;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object*);
extern lean_object* l_Lean_identKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1(lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__2;
lean_object* l_Lean_PrettyPrinter_format_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_Prelude___instance__72;
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___rarg(lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__2(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_try_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__1___boxed(lean_object*);
extern lean_object* l_Lean_nameLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9;
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Data_Repr___instance__18___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trimRight(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3099____closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2_match__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
extern lean_object* l_Lean_numLitKind___closed__1;
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_toggleInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg(lean_object*);
lean_object* l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg(lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_withoutForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Data_Repr___instance__15___closed__1;
extern lean_object* l_Std_Range___kind_term____x40_Init_Data_Range___hyg_108____closed__20;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatterAttribute;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5;
uint8_t l_Array_isEqvAux___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_inaccessible_user_name(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1(lean_object*);
lean_object* l_String_trimLeft(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter(lean_object*);
lean_object* l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object*, lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_Prelude___instance__73___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_State_leadWord___default;
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_FormatterM_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_FormatterM_orelse(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_getWidth___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*);
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg___boxed(lean_object**);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ReaderT_Init_Prelude___instance__50___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Name_isNum(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toStringWithSep___closed__1;
lean_object* l_Lean_Format_getIndent(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_format_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_pushTokenCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
extern lean_object* l_Array_Init_Data_Array_Basic___instance__3___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2355_(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
extern lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Lean_ParserCompiler_Attribute___instance__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1;
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_Lean_Data_Format___instance__4;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_KeyedDeclsAttribute_Lean_KeyedDeclsAttribute___instance__3___closed__1;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Core___instance__24;
lean_object* lean_simp_macro_scopes(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Init_Prelude___instance__40___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__2;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
lean_object* l_Lean_PrettyPrinter_Formatter_suppressInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Prelude___instance__47___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__3;
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__6;
extern lean_object* l_Lean_interpolatedStrLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_pushTokenCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__1(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_State_leadWord___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Init_Prelude___instance__73___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_State_stack___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_FormatterM_orelse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_22 = lean_nat_dec_eq(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
lean_dec(x_12);
x_23 = lean_st_ref_set(x_4, x_9, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
x_28 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_29 = lean_nat_dec_eq(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
x_31 = lean_st_ref_set(x_4, x_9, x_26);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_FormatterM_orelse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_FormatterM_orelse___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_FormatterM_orelse___rarg), 7, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1___closed__1;
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [formatter] argument, expected identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [formatter] argument, unknown syntax kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Init_Data_Repr___instance__15___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3;
x_14 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_13, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_29; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_15);
lean_inc(x_11);
x_29 = lean_environment_find(x_11, x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_16 = x_30;
goto block_28;
}
else
{
lean_dec(x_29);
if (x_1 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_16 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
block_28:
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = l_Lean_Parser_isValidSyntaxNodeKind(x_11, x_15);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_18 = l_System_FilePath_dirName___closed__1;
x_19 = l_Lean_Name_toStringWithSep(x_18, x_15);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_25, x_3, x_4, x_5, x_9);
return x_26;
}
else
{
lean_object* x_27; 
if (lean_is_scalar(x_10)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_10;
}
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinFormatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a formatter for a parser.\n\n  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9;
x_4 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8;
x_5 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("formatterAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11;
x_3 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("combinatorFormatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a formatter for a parser combinator.\n\n  [combinatorFormatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.\n  Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.\n  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\n  with `Formatter` in the parameter types.");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3;
x_4 = l_Lean_ParserCompiler_registerCombinatorAttribute(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_throwBacktrack(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__2___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
x_12 = lean_st_ref_set(x_3, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_ref_set(x_3, x_21, x_9);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_24 = lean_apply_1(x_2, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_23);
x_28 = lean_st_ref_set(x_4, x_27, x_10);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__3;
x_2 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__3___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__4;
x_2 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__5;
x_3 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__7;
return x_1;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_getStack(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_array_get_size(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_getStackSize(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_dec(x_11);
lean_ctor_set(x_8, 2, x_1);
x_12 = lean_st_ref_set(x_3, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_1);
x_22 = lean_st_ref_set(x_3, x_21, x_9);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_setStack(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_push(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = lean_array_push(x_11, x_1);
lean_ctor_set(x_8, 2, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = lean_array_push(x_22, x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_push___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_push(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_box(1);
x_7 = l_Lean_PrettyPrinter_Formatter_push(x_6, x_1, x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_Lean_Init_Prelude___instance__73___closed__1;
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_2, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = l_Lean_Init_Prelude___instance__73___closed__1;
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_st_ref_set(x_2, x_25, x_11);
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
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_left(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = l_Lean_Syntax_Traverser_left(x_18);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_st_ref_set(x_1, x_22, x_7);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_Syntax_Traverser_down(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_23 = l_Lean_Syntax_Traverser_down(x_20, x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_up(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = l_Lean_Syntax_Traverser_up(x_18);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_st_ref_set(x_1, x_22, x_7);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1;
x_11 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_6(x_10, x_15, x_2, x_3, x_4, x_5, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_12, x_17);
lean_dec(x_12);
x_19 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(x_18, x_2, x_3, x_4, x_5, x_9);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_apply_6(x_10, x_22, x_2, x_3, x_4, x_5, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_4, x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
lean_inc(x_9);
lean_inc(x_14);
x_17 = l_Array_extract___rarg(x_14, x_9, x_16);
x_18 = lean_apply_1(x_1, x_17);
x_19 = l_Array_shrink___rarg(x_14, x_9);
lean_dec(x_9);
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_PrettyPrinter_Formatter_setStack(x_20, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Format_isNil(x_4);
x_8 = 1;
x_9 = x_2 + x_8;
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_4);
x_2 = x_9;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
x_2 = x_9;
x_4 = x_6;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_concat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_fold(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_concat___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Format_Lean_Data_Format___instance__4;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_PrettyPrinter_Formatter_fold(x_8, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_Format_getIndent(x_11);
lean_dec(x_11);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_st_ref_take(x_4, x_10);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_array_pop(x_18);
x_20 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_push(x_19, x_21);
lean_ctor_set(x_15, 2, x_22);
x_23 = lean_st_ref_set(x_4, x_15, x_16);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
x_32 = lean_ctor_get(x_15, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
lean_inc(x_32);
x_33 = lean_array_pop(x_32);
x_34 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_32);
lean_dec(x_32);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_push(x_33, x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_st_ref_set(x_4, x_37, x_16);
lean_dec(x_4);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_13);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_dec(x_14);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
x_48 = lean_array_pop(x_47);
x_49 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_47);
lean_dec(x_47);
lean_inc(x_44);
x_50 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_push(x_48, x_50);
lean_ctor_set(x_43, 2, x_51);
x_52 = lean_st_ref_set(x_4, x_43, x_45);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_43, 0);
x_60 = lean_ctor_get(x_43, 1);
x_61 = lean_ctor_get(x_43, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_43);
lean_inc(x_61);
x_62 = lean_array_pop(x_61);
x_63 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_61);
lean_dec(x_61);
lean_inc(x_44);
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_44);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_push(x_62, x_64);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_st_ref_set(x_4, x_66, x_45);
lean_dec(x_4);
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
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_9);
if (x_72 == 0)
{
return x_9;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_9, 0);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_9);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
lean_object* l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_indent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_3);
x_8 = l_Lean_PrettyPrinter_Formatter_fold(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_array_pop(x_14);
x_16 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_14);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_push(x_15, x_18);
lean_ctor_set(x_11, 2, x_19);
x_20 = lean_st_ref_set(x_3, x_11, x_12);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
lean_inc(x_29);
x_30 = lean_array_pop(x_29);
x_31 = l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(x_29);
lean_dec(x_29);
x_32 = 1;
x_33 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_push(x_30, x_33);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_12);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_22 = lean_nat_dec_eq(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
lean_dec(x_12);
x_23 = lean_st_ref_set(x_4, x_9, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
x_28 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_29 = lean_nat_dec_eq(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
x_31 = lean_st_ref_set(x_4, x_9, x_26);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_formatter(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_pretty_printer_formatter_interpret_parser_descr(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_PrettyPrinter_formatterAttribute;
x_8 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_PrettyPrinter_runForNodeKind___rarg(x_7, x_1, x_8, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKind___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_formatterForKind(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = lean_box(0);
x_9 = l_Lean_Format_pretty(x_7, x_8);
x_10 = l_Lean_Format_Lean_Data_Format___instance__4;
x_11 = lean_array_get(x_10, x_2, x_1);
x_12 = l_Lean_Format_pretty(x_11, x_8);
x_13 = lean_string_dec_eq(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = x_4 + x_15;
x_4 = x_16;
goto _start;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_Syntax_getKind(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_2 + x_16;
x_2 = x_17;
x_4 = x_14;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_extract___rarg(x_2, x_11, x_10);
x_13 = l_Lean_PrettyPrinter_Formatter_setStack(x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Formatter.categoryParser.formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Formatter.visit: inequal choice children");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(185u);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_8 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_49 = l_Lean_Syntax_getArgs(x_2);
x_50 = lean_array_get_size(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
x_11 = x_10;
goto block_48;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_50, x_50);
if (x_53 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
x_11 = x_10;
goto block_48;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_56 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_49, x_54, x_55, x_56, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_49);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_11 = x_58;
goto block_48;
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_48:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_4, x_5, x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_nat_dec_lt(x_9, x_15);
lean_inc(x_9);
lean_inc(x_13);
x_17 = l_Array_toSubarray___rarg(x_13, x_9, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_9, x_13, x_22, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_18);
x_25 = lean_nat_dec_le(x_20, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_9, x_13, x_26, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
return x_27;
}
else
{
if (x_16 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_9, x_13, x_28, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
return x_29;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_31 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_32 = l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(x_9, x_13, x_18, x_30, x_31);
lean_dec(x_18);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_9, x_13, x_33, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = l_Init_Core___instance__24;
x_36 = l_Init_Prelude___instance__40___rarg(x_1, x_35);
x_37 = lean_alloc_closure((void*)(l_Init_Prelude___instance__47___rarg___boxed), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4;
x_39 = lean_panic_fn(x_37, x_38);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = lean_apply_5(x_39, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_9, x_13, x_41, x_3, x_4, x_5, x_6, x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_41);
lean_dec(x_9);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Syntax_getKind(x_3);
x_10 = l_Lean_choiceKind___closed__2;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep(x_12, x_1);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe), 6, 1);
lean_closure_set(x_18, 0, x_9);
x_19 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_17, x_18, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___boxed), 7, 1);
lean_closure_set(x_20, 0, x_2);
x_21 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1;
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___rarg), 7, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
x_23 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_22, x_4, x_5, x_6, x_7, x_8);
return x_23;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_2 = l_ReaderT_Init_Prelude___instance__50___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1;
x_2 = l_ReaderT_Init_Prelude___instance__50___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2;
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_indent___boxed), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_group(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_13);
lean_dec(x_13);
x_15 = lean_nat_sub(x_14, x_1);
lean_dec(x_14);
x_16 = l_Lean_Syntax_getArg(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
x_17 = l_Lean_Syntax_getId(x_16);
lean_dec(x_16);
x_18 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_17, x_2, x_3, x_4, x_5, x_9);
return x_18;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_error_formatter___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_error_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_try_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_lookahead_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(x_2, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_10);
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_PersistentArray_push___rarg(x_19, x_21);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_st_ref_set(x_6, x_13, x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_10);
lean_inc(x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_31, x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_30);
lean_ctor_set(x_13, 3, x_35);
x_36 = lean_st_ref_set(x_6, x_13, x_15);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_44 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_10);
lean_inc(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_PersistentArray_push___rarg(x_45, x_48);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_44);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_st_ref_set(x_6, x_51, x_15);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_checkTraceOption(x_7, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("backtrack");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected node kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = lean_name_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_free_object(x_7);
x_30 = lean_st_ref_get(x_5, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = 0;
x_13 = x_35;
x_14 = x_34;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_37, x_2, x_3, x_4, x_5, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_13 = x_41;
x_14 = x_40;
goto block_29;
}
block_29:
{
if (x_13 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_1);
x_15 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_26 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_25, x_24, x_2, x_3, x_4, x_5, x_14);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_27);
return x_28;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_1);
x_42 = lean_box(0);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = l_Lean_Syntax_getKind(x_43);
x_46 = lean_name_eq(x_1, x_45);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_st_ref_get(x_5, x_44);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 3);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = 0;
x_47 = x_69;
x_48 = x_68;
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_72 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_71, x_2, x_3, x_4, x_5, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_47 = x_75;
x_48 = x_74;
goto block_63;
}
block_63:
{
if (x_47 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_1);
x_49 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_51 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_1);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_60 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_59, x_58, x_2, x_3, x_4, x_5, x_48);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_61);
return x_62;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_45);
lean_dec(x_1);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_44);
return x_77;
}
}
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("foo");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___rarg), 7, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_12, x_4, x_5, x_6, x_7, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Init_Prelude___instance__73___closed__1;
x_2 = l_Lean_FileMap_ofString(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Init_Prelude___instance__73___closed__1;
x_12 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
lean_inc(x_14);
x_18 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_10);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*6, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*6 + 1, x_17);
x_19 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_20 = l_Lean_Parser_tokenFn(x_18, x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Init_Prelude___instance__73___closed__1;
x_25 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_inc(x_1);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(0u);
x_30 = 0;
lean_inc(x_27);
x_31 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*6 + 1, x_30);
x_32 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_33 = l_Lean_Parser_tokenFn(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
return x_34;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_parseToken(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_6 = lean_string_utf8_get(x_1, x_5);
x_7 = 32;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
else
{
return x_3;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushTokenCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_7);
x_10 = l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1(x_1, x_8, x_7);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Substring_beq(x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_PrettyPrinter_Formatter_pushLine(x_2, x_3, x_4, x_5, x_6);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_String_trimRight(x_1);
lean_dec(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_push(x_16, x_2, x_3, x_4, x_5, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_1);
x_19 = l_Lean_PrettyPrinter_Formatter_push(x_18, x_2, x_3, x_4, x_5, x_6);
return x_19;
}
}
}
lean_object* l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushTokenCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
lean_dec(x_8);
x_54 = l_Lean_Init_Prelude___instance__73___closed__1;
x_55 = lean_string_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_String_trimRight(x_1);
x_57 = lean_string_dec_eq(x_56, x_1);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_53);
x_58 = lean_box(0);
x_10 = x_58;
goto block_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = l_String_trimLeft(x_1);
lean_inc(x_59);
x_60 = lean_string_append(x_59, x_53);
lean_dec(x_53);
x_61 = l_Lean_PrettyPrinter_Formatter_parseToken(x_60, x_2, x_3, x_4, x_5, x_9);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_string_utf8_byte_size(x_59);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_67 = l_Init_Data_Repr___instance__18___closed__2;
lean_inc(x_1);
x_68 = lean_string_append(x_1, x_67);
x_69 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_68, x_2, x_3, x_4, x_5, x_63);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_st_ref_take(x_3, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_dec(x_75);
x_76 = lean_string_dec_eq(x_59, x_1);
lean_dec(x_59);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_1);
lean_ctor_set(x_72, 1, x_54);
x_77 = lean_st_ref_set(x_3, x_72, x_73);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_ctor_set(x_72, 1, x_1);
x_84 = lean_st_ref_set(x_3, x_72, x_73);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_72, 0);
x_92 = lean_ctor_get(x_72, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_72);
x_93 = lean_string_dec_eq(x_59, x_1);
lean_dec(x_59);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_1);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_54);
lean_ctor_set(x_94, 2, x_92);
x_95 = lean_st_ref_set(x_3, x_94, x_73);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_91);
lean_ctor_set(x_100, 1, x_1);
lean_ctor_set(x_100, 2, x_92);
x_101 = lean_st_ref_set(x_3, x_100, x_73);
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
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_inc(x_1);
x_106 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_1, x_2, x_3, x_4, x_5, x_63);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_3, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_109, 1);
x_113 = lean_string_dec_eq(x_59, x_1);
lean_dec(x_59);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
lean_dec(x_112);
lean_dec(x_1);
lean_ctor_set(x_109, 1, x_54);
x_114 = lean_st_ref_set(x_3, x_109, x_110);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
x_117 = lean_box(0);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_string_append(x_1, x_112);
lean_dec(x_112);
lean_ctor_set(x_109, 1, x_121);
x_122 = lean_st_ref_set(x_3, x_109, x_110);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_dec(x_124);
x_125 = lean_box(0);
lean_ctor_set(x_122, 0, x_125);
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
lean_dec(x_122);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_109, 0);
x_130 = lean_ctor_get(x_109, 1);
x_131 = lean_ctor_get(x_109, 2);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_109);
x_132 = lean_string_dec_eq(x_59, x_1);
lean_dec(x_59);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_130);
lean_dec(x_1);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_54);
lean_ctor_set(x_133, 2, x_131);
x_134 = lean_st_ref_set(x_3, x_133, x_110);
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
x_137 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_string_append(x_1, x_130);
lean_dec(x_130);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_129);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_131);
x_141 = lean_st_ref_set(x_3, x_140, x_110);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
}
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_53);
x_146 = lean_box(0);
x_10 = x_146;
goto block_52;
}
block_52:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_10);
lean_inc(x_1);
x_11 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_1, x_2, x_3, x_4, x_5, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
x_18 = l_String_trimLeft(x_1);
x_19 = lean_string_dec_eq(x_18, x_1);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_20 = l_Lean_Init_Prelude___instance__73___closed__1;
lean_ctor_set(x_14, 1, x_20);
x_21 = lean_st_ref_set(x_3, x_14, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_ctor_set(x_14, 1, x_1);
x_28 = lean_st_ref_set(x_3, x_14, x_15);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = l_String_trimLeft(x_1);
x_38 = lean_string_dec_eq(x_37, x_1);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_39 = l_Lean_Init_Prelude___instance__73___closed__1;
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_36);
x_41 = lean_st_ref_set(x_3, x_40, x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_36);
x_47 = lean_st_ref_set(x_3, x_46, x_15);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected symbol '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isToken(x_1, x_8);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_get(x_5, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = 0;
x_11 = x_33;
x_12 = x_32;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_35, x_2, x_3, x_4, x_5, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_11 = x_39;
x_12 = x_38;
goto block_27;
}
block_27:
{
if (x_11 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_24 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_23, x_22, x_2, x_3, x_4, x_5, x_12);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_25);
return x_26;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
x_40 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_2, x_3, x_4, x_5, x_9);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_3, x_4, x_5, x_41);
return x_42;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(x_1, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not an atom: ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__4;
x_13 = l_String_trim(x_1);
x_14 = lean_string_dec_eq(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = l_Lean_PrettyPrinter_Formatter_pushToken(x_2, x_3, x_4, x_5, x_6, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_12, x_16, x_3, x_4, x_5, x_6, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_19 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_3, x_4, x_5, x_6, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_6(x_12, x_20, x_3, x_4, x_5, x_6, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = 0;
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_formatStxAux(x_24, x_25, x_26, x_9);
x_28 = lean_box(0);
x_29 = l_Lean_Format_pretty(x_27, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg(x_33, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
uint8_t l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(x_1, x_4);
x_6 = l_Lean_Name_isNum(x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
static lean_object* _init_l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("«");
return x_1;
}
}
static lean_object* _init_l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("»");
return x_1;
}
}
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep(x_6, x_4);
x_8 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(x_5);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_13);
x_17 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
uint8_t l_Array_isEqvAux___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_Syntax_structEq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_identKind;
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind(x_6, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getId(x_10);
lean_inc(x_12);
x_13 = lean_simp_macro_scopes(x_12);
x_14 = l_System_FilePath_dirName___closed__1;
lean_inc(x_13);
x_15 = l_Lean_Name_toStringWithSep(x_14, x_13);
x_16 = l_Lean_Name_isAnonymous(x_13);
if (x_16 == 0)
{
uint8_t x_17; 
lean_inc(x_13);
x_17 = lean_is_inaccessible_user_name(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_18 = l_Lean_Name_components(x_13);
x_19 = 0;
x_20 = l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Array_Init_Data_Array_Basic___instance__3___rarg___closed__1;
x_22 = l_String_isPrefixOf(x_21, x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_15);
x_23 = l_Lean_PrettyPrinter_Formatter_parseToken(x_15, x_1, x_2, x_3, x_4, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_10);
x_28 = lean_array_push(x_27, x_10);
x_29 = lean_array_get_size(x_26);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
x_32 = l_Lean_Name_components(x_12);
x_33 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(x_32);
x_34 = lean_box(0);
x_35 = l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(x_34, x_33);
x_36 = l_Lean_Name_toStringWithSep(x_14, x_35);
x_37 = l_Lean_PrettyPrinter_Formatter_pushToken(x_36, x_1, x_2, x_3, x_4, x_25);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_38);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_isEqvAux___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__3(x_10, x_24, lean_box(0), x_26, x_28, x_40);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_10);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_15);
x_42 = l_Lean_Name_components(x_12);
x_43 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(x_42);
x_44 = lean_box(0);
x_45 = l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(x_44, x_43);
x_46 = l_Lean_Name_toStringWithSep(x_14, x_45);
x_47 = l_Lean_PrettyPrinter_Formatter_pushToken(x_46, x_1, x_2, x_3, x_4, x_25);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
x_50 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_1, x_2, x_3, x_4, x_25);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_12);
lean_dec(x_10);
x_53 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_1, x_2, x_3, x_4, x_11);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_12);
lean_dec(x_10);
x_56 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_1, x_2, x_3, x_4, x_11);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_59 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_1, x_2, x_3, x_4, x_11);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_62 = l_Lean_Name_toStringWithSep___closed__1;
x_63 = l_Lean_PrettyPrinter_Formatter_pushToken(x_62, x_1, x_2, x_3, x_4, x_11);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_7);
if (x_66 == 0)
{
return x_7;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_7, 0);
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_7);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
lean_object* l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_isEqvAux___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_identKind;
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind(x_6, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep(x_13, x_12);
x_15 = l_Lean_PrettyPrinter_Formatter_pushToken(x_14, x_1, x_2, x_3, x_4, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_identEq_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitAtom_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = l_Lean_Init_Prelude___instance__72;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_21, x_23);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 2)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_PrettyPrinter_Formatter_pushToken(x_25, x_3, x_4, x_5, x_6, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_4, x_5, x_6, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_24);
x_29 = lean_box(0);
x_8 = x_29;
goto block_20;
}
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_PrettyPrinter_Formatter_pushToken(x_30, x_3, x_4, x_5, x_6, x_7);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_4, x_5, x_6, x_32);
return x_33;
}
default: 
{
lean_object* x_34; 
x_34 = lean_box(0);
x_8 = x_34;
goto block_20;
}
}
block_20:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = 0;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_formatStxAux(x_9, x_10, x_11, x_1);
x_13 = lean_box(0);
x_14 = l_Lean_Format_pretty(x_12, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___rarg(x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_8, x_13, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_8, x_20, x_2, x_3, x_4, x_5, x_9);
return x_21;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_charLitKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_strLitKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_nameLitKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_numLitKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_fieldIdxKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_many_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed), 8, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_many1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_many_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_optional_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_8);
x_11 = l_Lean_nullKind;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Formatter_many_formatter(x_1, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
}
}
lean_object* l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_mod(x_11, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_3 = x_12;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_12;
x_8 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = l_List_range(x_12);
x_14 = l_List_reverse___rarg(x_13);
x_15 = lean_alloc_closure((void*)(l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed), 8, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_15, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
}
lean_object* l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_sepBy_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withoutPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_withForbidden_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withoutForbidden_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_setExpected_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_toggleInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_suppressInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Init_Prelude___instance__73___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_6);
x_13 = l_Lean_PrettyPrinter_Formatter_pushLine(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_box(0);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Init_Prelude___instance__73___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_PrettyPrinter_Formatter_pushLine(x_1, x_2, x_3, x_4, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
x_10 = l_Lean_Init_Prelude___instance__73___closed__1;
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = l_Lean_Init_Prelude___instance__73___closed__1;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_eoi_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_skip_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_left(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = l_Lean_Syntax_Traverser_left(x_18);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_st_ref_set(x_1, x_22, x_7);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Lean_interpolatedStrLitKind;
x_14 = l_Lean_Syntax_isLit_x3f(x_13, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_push(x_26, x_6, x_7, x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_pushNone_formatter___spec__1___rarg(x_7, x_8, x_9, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = x_3 + x_32;
x_3 = x_33;
x_5 = x_30;
x_10 = x_31;
goto _start;
}
}
else
{
lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_10);
return x_35;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = l_Array_reverse___rarg(x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
x_16 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_15, x_2, x_3, x_4, x_5, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_18 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
x_19 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_18, x_2, x_3, x_4, x_5, x_9);
return x_19;
}
else
{
size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1;
x_23 = lean_box_usize(x_20);
x_24 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2___boxed), 10, 5);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_11);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_21);
x_25 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_24, x_2, x_3, x_4, x_5, x_9);
return x_25;
}
}
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_PrettyPrinter_Formatter_ite___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_apply_2(x_2, x_27, x_28);
return x_29;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_2(x_3, x_30, x_31);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_apply_1(x_4, x_33);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_apply_1(x_5, x_35);
return x_36;
}
case 4:
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_apply_1(x_6, x_37);
return x_38;
}
case 5:
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_apply_1(x_8, x_39);
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_apply_1(x_9, x_41);
return x_42;
}
case 7:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_46 = lean_box(x_45);
x_47 = lean_apply_3(x_10, x_43, x_44, x_46);
return x_47;
}
case 8:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_51 = lean_box(x_50);
x_52 = lean_apply_3(x_11, x_48, x_49, x_51);
return x_52;
}
case 9:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_apply_3(x_12, x_53, x_54, x_55);
return x_56;
}
case 10:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec(x_1);
x_60 = lean_apply_3(x_13, x_57, x_58, x_59);
return x_60;
}
case 11:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_apply_1(x_14, x_61);
return x_62;
}
case 12:
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_65 = lean_box(x_64);
x_66 = lean_apply_2(x_21, x_63, x_65);
return x_66;
}
case 13:
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_apply_1(x_22, x_67);
return x_68;
}
case 14:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_apply_1(x_15, x_69);
return x_70;
}
case 15:
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
x_72 = lean_apply_1(x_16, x_71);
return x_72;
}
case 16:
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
x_74 = lean_apply_1(x_17, x_73);
return x_74;
}
case 17:
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_apply_1(x_18, x_75);
return x_76;
}
case 18:
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = lean_apply_1(x_20, x_77);
return x_78;
}
case 19:
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_apply_1(x_19, x_79);
return x_80;
}
case 20:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_apply_2(x_26, x_81, x_82);
return x_83;
}
case 21:
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
lean_dec(x_1);
x_85 = lean_apply_1(x_25, x_84);
return x_85;
}
case 22:
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_apply_1(x_7, x_86);
return x_87;
}
case 23:
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_apply_1(x_23, x_88);
return x_89;
}
default: 
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_91 = lean_box(x_90);
x_92 = lean_apply_1(x_24, x_91);
return x_92;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg___boxed), 26, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
_start:
{
lean_object* x_27; 
x_27 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_27;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_many_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_many_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_sepBy_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_sepBy_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_numLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_numLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_strLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_strLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_charLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_charLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_nameLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_identKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_identKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__1;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__3;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 4, 0);
return x_1;
}
}
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_pretty_printer_formatter_interpret_parser_descr(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_pretty_printer_formatter_interpret_parser_descr(x_6, x_2, x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_28 = lean_pretty_printer_formatter_interpret_parser_descr(x_26, x_2, x_3, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_pretty_printer_formatter_interpret_parser_descr(x_27, x_2, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2), 7, 2);
lean_closure_set(x_34, 0, x_29);
lean_closure_set(x_34, 1, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2), 7, 2);
lean_closure_set(x_37, 0, x_29);
lean_closure_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_29);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 2:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_pretty_printer_formatter_interpret_parser_descr(x_47, x_2, x_3, x_4);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3), 6, 1);
lean_closure_set(x_51, 0, x_50);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3), 6, 1);
lean_closure_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 3:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_pretty_printer_formatter_interpret_parser_descr(x_60, x_2, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed), 5, 1);
lean_closure_set(x_64, 0, x_63);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed), 5, 1);
lean_closure_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
return x_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 4:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = lean_pretty_printer_formatter_interpret_parser_descr(x_73, x_2, x_3, x_4);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5), 6, 1);
lean_closure_set(x_77, 0, x_76);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5), 6, 1);
lean_closure_set(x_80, 0, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
return x_74;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
case 5:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_pretty_printer_formatter_interpret_parser_descr(x_86, x_2, x_3, x_4);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6), 6, 1);
lean_closure_set(x_90, 0, x_89);
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6), 6, 1);
lean_closure_set(x_93, 0, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
return x_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_87);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
case 6:
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
lean_dec(x_1);
x_100 = lean_pretty_printer_formatter_interpret_parser_descr(x_99, x_2, x_3, x_4);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7), 6, 1);
lean_closure_set(x_103, 0, x_102);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7), 6, 1);
lean_closure_set(x_106, 0, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
return x_100;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_100, 0);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_100);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
case 7:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_114 = lean_pretty_printer_formatter_interpret_parser_descr(x_112, x_2, x_3, x_4);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_pretty_printer_formatter_interpret_parser_descr(x_113, x_2, x_3, x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_120, 0, x_115);
lean_closure_set(x_120, 1, x_119);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_117);
x_123 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_123, 0, x_115);
lean_closure_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_115);
x_125 = !lean_is_exclusive(x_117);
if (x_125 == 0)
{
return x_117;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_117, 0);
x_127 = lean_ctor_get(x_117, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_117);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_113);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_114);
if (x_129 == 0)
{
return x_114;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_114, 0);
x_131 = lean_ctor_get(x_114, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_114);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 8:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 1);
lean_inc(x_134);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_135 = lean_pretty_printer_formatter_interpret_parser_descr(x_133, x_2, x_3, x_4);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_pretty_printer_formatter_interpret_parser_descr(x_134, x_2, x_3, x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9), 7, 2);
lean_closure_set(x_141, 0, x_136);
lean_closure_set(x_141, 1, x_140);
lean_ctor_set(x_138, 0, x_141);
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__9), 7, 2);
lean_closure_set(x_144, 0, x_136);
lean_closure_set(x_144, 1, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
uint8_t x_146; 
lean_dec(x_136);
x_146 = !lean_is_exclusive(x_138);
if (x_146 == 0)
{
return x_138;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_138, 0);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_138);
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
lean_dec(x_134);
lean_dec(x_3);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_135);
if (x_150 == 0)
{
return x_135;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_135, 0);
x_152 = lean_ctor_get(x_135, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_135);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
case 9:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_1, 2);
lean_inc(x_155);
lean_dec(x_1);
x_156 = lean_pretty_printer_formatter_interpret_parser_descr(x_155, x_2, x_3, x_4);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10), 7, 2);
lean_closure_set(x_159, 0, x_154);
lean_closure_set(x_159, 1, x_158);
lean_ctor_set(x_156, 0, x_159);
return x_156;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_156);
x_162 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__10), 7, 2);
lean_closure_set(x_162, 0, x_154);
lean_closure_set(x_162, 1, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
uint8_t x_164; 
lean_dec(x_154);
x_164 = !lean_is_exclusive(x_156);
if (x_164 == 0)
{
return x_156;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_156, 0);
x_166 = lean_ctor_get(x_156, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_156);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
case 10:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_1, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_1, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 2);
lean_inc(x_170);
lean_dec(x_1);
x_171 = lean_pretty_printer_formatter_interpret_parser_descr(x_170, x_2, x_3, x_4);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11___boxed), 8, 3);
lean_closure_set(x_174, 0, x_168);
lean_closure_set(x_174, 1, x_169);
lean_closure_set(x_174, 2, x_173);
lean_ctor_set(x_171, 0, x_174);
return x_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_171, 0);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_171);
x_177 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11___boxed), 8, 3);
lean_closure_set(x_177, 0, x_168);
lean_closure_set(x_177, 1, x_169);
lean_closure_set(x_177, 2, x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
uint8_t x_179; 
lean_dec(x_169);
lean_dec(x_168);
x_179 = !lean_is_exclusive(x_171);
if (x_179 == 0)
{
return x_171;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_171, 0);
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_171);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
case 11:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_3);
lean_dec(x_2);
x_183 = lean_ctor_get(x_1, 0);
lean_inc(x_183);
lean_dec(x_1);
x_184 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__12___boxed), 6, 1);
lean_closure_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_4);
return x_185;
}
case 12:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_ctor_get(x_1, 0);
lean_inc(x_186);
lean_dec(x_1);
x_187 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__13___boxed), 6, 1);
lean_closure_set(x_187, 0, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_4);
return x_188;
}
case 13:
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_3);
lean_dec(x_2);
x_189 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__1;
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_4);
return x_190;
}
case 14:
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_3);
lean_dec(x_2);
x_191 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__2;
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_4);
return x_192;
}
case 15:
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_3);
lean_dec(x_2);
x_193 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__3;
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_4);
return x_194;
}
case 16:
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_3);
lean_dec(x_2);
x_195 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__4;
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_4);
return x_196;
}
case 17:
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_3);
lean_dec(x_2);
x_197 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__5;
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_4);
return x_198;
}
case 18:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
lean_dec(x_1);
x_200 = lean_pretty_printer_formatter_interpret_parser_descr(x_199, x_2, x_3, x_4);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__18), 6, 1);
lean_closure_set(x_203, 0, x_202);
lean_ctor_set(x_200, 0, x_203);
return x_200;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_200, 0);
x_205 = lean_ctor_get(x_200, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_200);
x_206 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__18), 6, 1);
lean_closure_set(x_206, 0, x_204);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_200);
if (x_208 == 0)
{
return x_200;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_200, 0);
x_210 = lean_ctor_get(x_200, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_200);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
case 19:
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_3);
lean_dec(x_2);
x_212 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__6;
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_4);
return x_213;
}
case 20:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_ctor_get(x_1, 0);
lean_inc(x_214);
lean_dec(x_1);
x_215 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__20), 6, 1);
lean_closure_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_4);
return x_216;
}
case 21:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
lean_dec(x_1);
x_218 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
x_219 = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(x_218, x_217, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_219;
}
case 22:
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_1, 0);
lean_inc(x_220);
lean_dec(x_1);
x_221 = lean_pretty_printer_formatter_interpret_parser_descr(x_220, x_2, x_3, x_4);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___boxed), 5, 1);
lean_closure_set(x_224, 0, x_223);
lean_ctor_set(x_221, 0, x_224);
return x_221;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 0);
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_221);
x_227 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___boxed), 5, 1);
lean_closure_set(x_227, 0, x_225);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_221);
if (x_229 == 0)
{
return x_221;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_221, 0);
x_231 = lean_ctor_get(x_221, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_221);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 23:
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_1, 0);
lean_inc(x_233);
lean_dec(x_1);
x_234 = lean_pretty_printer_formatter_interpret_parser_descr(x_233, x_2, x_3, x_4);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_234, 0);
x_237 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__22), 6, 1);
lean_closure_set(x_237, 0, x_236);
lean_ctor_set(x_234, 0, x_237);
return x_234;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_234, 0);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_234);
x_240 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__22), 6, 1);
lean_closure_set(x_240, 0, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_234);
if (x_242 == 0)
{
return x_234;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_234, 0);
x_244 = lean_ctor_get(x_234, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_234);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
default: 
{
uint8_t x_246; 
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__7;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_4);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__8;
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_4);
return x_250;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__21(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_format_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("format: uncaught backtrack exception");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_format___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_format(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_builtinTokenTable;
x_8 = lean_st_ref_get(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_13 = l_Lean_Init_Prelude___instance__73___closed__1;
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_st_mk_ref(x_15, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_20 = l_Lean_PrettyPrinter_Formatter_fold(x_19, x_1, x_11, x_17, x_3, x_4, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_17, x_21);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Format_Lean_Data_Format___instance__4;
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get(x_26, x_25, x_27);
lean_dec(x_25);
x_29 = 1;
x_30 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Format_Lean_Data_Format___instance__4;
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get(x_34, x_33, x_35);
lean_dec(x_33);
x_37 = 1;
x_38 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_17);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_20, 0);
lean_dec(x_42);
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_20, 1);
x_47 = lean_ctor_get(x_20, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_50 = lean_nat_dec_eq(x_49, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_20);
lean_dec(x_40);
x_51 = l_Lean_PrettyPrinter_format___closed__3;
x_52 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_51, x_3, x_4, x_46);
lean_dec(x_4);
lean_dec(x_3);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_dec(x_20);
x_54 = lean_ctor_get(x_40, 0);
lean_inc(x_54);
x_55 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_56 = lean_nat_dec_eq(x_55, x_54);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_40);
x_58 = l_Lean_PrettyPrinter_format___closed__3;
x_59 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_58, x_3, x_4, x_53);
lean_dec(x_4);
lean_dec(x_3);
return x_59;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_108____closed__20;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_formatTerm___closed__1;
x_6 = l_Lean_PrettyPrinter_format(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3099____closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_formatCommand___closed__1;
x_6 = l_Lean_PrettyPrinter_format(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2355_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter_Formatter(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Formatter_State_leadWord___default = _init_l_Lean_PrettyPrinter_Formatter_State_leadWord___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_State_leadWord___default);
l_Lean_PrettyPrinter_Formatter_State_stack___default = _init_l_Lean_PrettyPrinter_Formatter_State_stack___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_State_stack___default);
l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1___closed__1 = _init_l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Lean_PrettyPrinter_Formatter___instance__1___closed__1);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13);
res = l_Lean_PrettyPrinter_mkFormatterAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_formatterAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3);
res = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_combinatorFormatterAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorFormatterAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__1);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__2);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__3);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__4);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__5);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__6);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2___closed__7);
l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2 = _init_l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_Lean_PrettyPrinter_Formatter___instance__2);
l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1);
l_Lean_PrettyPrinter_Formatter_concat___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_concat___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_concat___closed__1);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__3___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__1);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__2);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__3);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__4);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__5);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__6);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__7);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__8 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__8);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__1);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__4);
l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1 = _init_l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1();
lean_mark_persistent(l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1);
l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2 = _init_l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2();
lean_mark_persistent(l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2);
l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1 = _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__2);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__14___closed__3);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__2);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__15___closed__3);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__2);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__16___closed__3);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__2);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__17___closed__3);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__2);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__19___closed__3);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__1);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__2);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__3);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__4);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__5);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__6);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__7);
l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__8 = _init_l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___closed__8);
l_Lean_PrettyPrinter_format___closed__1 = _init_l_Lean_PrettyPrinter_format___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__1);
l_Lean_PrettyPrinter_format___closed__2 = _init_l_Lean_PrettyPrinter_format___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__2);
l_Lean_PrettyPrinter_format___closed__3 = _init_l_Lean_PrettyPrinter_format___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__3);
l_Lean_PrettyPrinter_formatTerm___closed__1 = _init_l_Lean_PrettyPrinter_formatTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTerm___closed__1);
l_Lean_PrettyPrinter_formatCommand___closed__1 = _init_l_Lean_PrettyPrinter_formatCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__1);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2355_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
