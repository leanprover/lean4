// Lean compiler output
// Module: Lean.PrettyPrinter.Formatter
// Imports: Init Lean.Parser.Extension Lean.KeyedDeclsAttribute Lean.ParserCompiler.Attribute
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
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getOptions___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__14;
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object*);
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_Def_inhabited___closed__2;
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__1(lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__4;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__6;
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_try_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1;
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1;
lean_object* lean_io_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object*);
lean_object* l___private_Lean_PrettyPrinter_Formatter_1__regTraceClasses(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concatArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__10;
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trimRight(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_unquotedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_toggleInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_termParser___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__13;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
uint8_t l_Lean_Syntax_structEq___main(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unquotedSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__1;
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__11;
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
extern lean_object* l_Lean_Format_Inhabited;
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trimLeft(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__2;
extern lean_object* l_Lean_quotedSymbolKind;
lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Meta_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__7;
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__2;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_formatCommand___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1;
extern lean_object* l_Lean_formatDataValue___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_formatterAttribute___closed__3;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatterAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__12;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___boxed(lean_object*);
extern lean_object* l_Lean_Format_getWidth___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__2;
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__3;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3;
extern lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
lean_object* l_Lean_PrettyPrinter_formatCommand___closed__3;
lean_object* l_Lean_PrettyPrinter_formatterAttribute___closed__1;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_PUnit_Inhabited;
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_Core_addContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatterAttribute___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__9;
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_formatterAttribute___spec__2(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_Core_getTraceState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatterAttribute___closed__2;
lean_object* l_Array_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [formatter] argument, expected identifier");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [formatter] argument, unknown syntax kind '");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2;
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_isValidSyntaxNodeKind(x_2, x_6);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_6);
x_10 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_16);
lean_inc(x_2);
x_17 = lean_environment_find(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Parser_isValidSyntaxNodeKind(x_2, x_16);
lean_dec(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_16);
x_21 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_16);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_16);
return x_27;
}
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinFormatter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("formatter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Formatter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a formatter for a parser.\n\n[formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11() {
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
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("formatterAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13() {
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
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_formatterAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatterAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_formatterAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatterAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_PrettyPrinter_formatterAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatterAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_formatterAttribute___closed__3;
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
lean_object* _init_l_Lean_PrettyPrinter_formatterAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_KeyedDeclsAttribute_Def_inhabited___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_PrettyPrinter_formatterAttribute___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("combinatorFormatter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a formatter for a parser combinator.\n\n[combinatorFormatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.\nNote that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.\nThe tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\nwith `Formatter` in the parameter types.");
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
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_apply_1(x_1, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = lean_apply_1(x_1, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__3___rarg), 9, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_apply_1(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_4, 0, x_14);
lean_ctor_set(x_12, 1, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_23 = lean_apply_1(x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateT_get___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__1___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__3;
x_2 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__3___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__2___boxed), 8, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__3___boxed), 9, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__4;
x_2 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__5;
x_3 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__7;
return x_1;
}
}
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_StateT_get___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_ReaderT_lift___at_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_array_get_size(x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = lean_array_get_size(x_19);
lean_dec(x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
lean_ctor_set(x_3, 2, x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_setStack(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_push(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_array_push(x_10, x_1);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = lean_array_push(x_17, x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_push___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_push(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_Syntax_Traverser_left(x_8);
lean_ctor_set(x_1, 0, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = l_Lean_Syntax_Traverser_left(x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = l_Lean_Syntax_Traverser_down(x_10, x_1);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = l_Lean_Syntax_Traverser_down(x_15, x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_Syntax_Traverser_up(x_8);
lean_ctor_set(x_1, 0, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = l_Lean_Syntax_Traverser_up(x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_13, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_15, x_19);
lean_dec(x_15);
x_21 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(x_20, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = lean_apply_7(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_28, x_4, x_5, x_6, x_7, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_32, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_15 = lean_apply_7(x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_18, x_5, x_6, x_7, x_8, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_array_get_size(x_22);
lean_inc(x_13);
x_25 = l_Array_extract___rarg(x_22, x_13, x_24);
lean_dec(x_24);
x_26 = lean_apply_1(x_1, x_25);
x_27 = l_Array_shrink___main___rarg(x_22, x_13);
lean_dec(x_13);
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_PrettyPrinter_Formatter_setStack(x_28, x_3, x_23, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_concat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_concat___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_concat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Array_foldl___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PrettyPrinter_Formatter_concat___closed__2;
x_10 = l_Lean_PrettyPrinter_Formatter_fold(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_concatArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_PrettyPrinter_Formatter_concat(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("BACKTRACK");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 2)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_21; 
lean_free_object(x_10);
lean_dec(x_11);
x_21 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_11);
x_27 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_10, 0);
lean_dec(x_33);
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_10, 0);
lean_dec(x_37);
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_10, 0);
lean_dec(x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_11);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_mk_antiquot_formatter(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no known formatter for kind '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Core_getEnv___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_formatterAttribute;
x_13 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_12, x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Core_getConstInfo___closed__5;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_throwError___rarg(x_18, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_apply_7(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_25;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = l_Lean_Syntax_getKind(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l_Lean_PrettyPrinter_Formatter_formatterForKind(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
x_4 = x_20;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Options_empty;
x_10 = l_Lean_Format_pretty(x_8, x_9);
x_11 = l_Lean_Format_Inhabited;
x_12 = lean_array_get(x_11, x_2, x_1);
x_13 = l_Lean_Format_pretty(x_12, x_9);
x_14 = lean_string_dec_eq(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_fget(x_4, x_6);
x_10 = l_Lean_Options_empty;
x_11 = l_Lean_Format_pretty(x_9, x_10);
x_12 = l_Lean_Format_Inhabited;
x_13 = lean_array_get(x_12, x_2, x_1);
x_14 = l_Lean_Format_pretty(x_13, x_10);
x_15 = lean_string_dec_eq(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = 1;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_18;
goto _start;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_apply_8(x_2, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___rarg), 9, 0);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Formatter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Formatter.visit: inequal choice children");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(204u);
x_3 = lean_unsigned_to_nat(6u);
x_4 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Syntax_getArgs(x_2);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l_Array_forMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(x_15, x_16, x_3, x_14, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_20, x_5, x_6, x_7, x_8, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_array_get_size(x_24);
x_27 = lean_nat_dec_lt(x_13, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_13, x_28);
lean_dec(x_13);
x_30 = l_Array_extract___rarg(x_24, x_16, x_29);
lean_dec(x_29);
lean_dec(x_24);
x_31 = l_Lean_PrettyPrinter_Formatter_setStack(x_30, x_3, x_25, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_26, x_26);
if (x_32 == 0)
{
uint8_t x_33; 
lean_inc(x_13);
x_33 = l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_13, x_24, x_24, x_26, x_13);
lean_dec(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_13, x_34);
lean_dec(x_13);
x_36 = l_Array_extract___rarg(x_24, x_16, x_35);
lean_dec(x_35);
lean_dec(x_24);
x_37 = l_Lean_PrettyPrinter_Formatter_setStack(x_36, x_3, x_25, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = l_PUnit_Inhabited;
x_39 = l_monadInhabited___rarg(x_1, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3;
x_42 = lean_panic_fn(x_40, x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_43 = lean_apply_7(x_42, x_3, x_25, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_13, x_47);
lean_dec(x_13);
x_49 = l_Array_extract___rarg(x_24, x_16, x_48);
lean_dec(x_48);
lean_dec(x_24);
x_50 = l_Lean_PrettyPrinter_Formatter_setStack(x_49, x_3, x_46, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_inc(x_13);
x_55 = l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_13, x_24, lean_box(0), x_24, x_26, x_13);
lean_dec(x_26);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_13, x_56);
lean_dec(x_13);
x_58 = l_Array_extract___rarg(x_24, x_16, x_57);
lean_dec(x_57);
lean_dec(x_24);
x_59 = l_Lean_PrettyPrinter_Formatter_setStack(x_58, x_3, x_25, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = l_PUnit_Inhabited;
x_61 = l_monadInhabited___rarg(x_1, x_60);
x_62 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_62, 0, x_61);
x_63 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3;
x_64 = lean_panic_fn(x_62, x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_65 = lean_apply_7(x_64, x_3, x_25, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_13, x_69);
lean_dec(x_13);
x_71 = l_Array_extract___rarg(x_24, x_16, x_70);
lean_dec(x_70);
lean_dec(x_24);
x_72 = l_Lean_PrettyPrinter_Formatter_setStack(x_71, x_3, x_68, x_5, x_6, x_7, x_8, x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_65);
if (x_73 == 0)
{
return x_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_65, 0);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_65);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_17);
if (x_77 == 0)
{
return x_17;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_17, 0);
x_79 = lean_ctor_get(x_17, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_17);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___boxed), 9, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__4;
x_2 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Syntax_getKind(x_12);
x_15 = l_Lean_choiceKind___closed__2;
x_16 = lean_name_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_1);
x_19 = lean_box(0);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 7, 3);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKind), 8, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_22, x_23, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_1);
x_25 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__5;
x_26 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_25, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
return x_26;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_anyRangeMAux___main___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_12);
lean_dec(x_12);
x_14 = lean_nat_sub(x_13, x_1);
lean_dec(x_13);
x_15 = l_Lean_Syntax_getArg(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
x_16 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_try_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_7(x_1, x_3, x_13, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l_Lean_Core_addContext___rarg(x_2, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_io_ref_take(x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 2);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_11);
x_22 = l_Std_PersistentArray_push___rarg(x_20, x_21);
lean_ctor_set(x_15, 0, x_22);
x_23 = lean_io_ref_set(x_8, x_14, x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_11);
x_35 = l_Std_PersistentArray_push___rarg(x_33, x_34);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_32);
lean_ctor_set(x_14, 2, x_36);
x_37 = lean_io_ref_set(x_8, x_14, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_47 = x_15;
} else {
 lean_dec_ref(x_15);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_11);
x_49 = l_Std_PersistentArray_push___rarg(x_46, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_45);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_io_ref_set(x_8, x_51, x_16);
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
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Core_getOptions___rarg(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_checkTraceOption(x_7, x_1);
lean_dec(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = l_Lean_checkTraceOption(x_10, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("backtrack");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected node kind '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = l_Lean_Syntax_getKind(x_14);
x_16 = lean_name_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Lean_Core_getTraceState___rarg(x_7, x_11);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = 0;
x_52 = lean_box(x_51);
lean_ctor_set(x_10, 0, x_52);
x_17 = x_10;
x_18 = x_50;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_55 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_54, x_6, x_7, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_10, 0, x_56);
x_17 = x_10;
x_18 = x_57;
goto block_46;
}
block_46:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_1);
x_21 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
if (lean_is_scalar(x_12)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_12;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_12);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_15);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__11;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__14;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Name_toStringWithSep___main(x_24, x_1);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Core_getConstInfo___closed__5;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_39 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_38, x_37, x_2, x_23, x_4, x_5, x_6, x_7, x_18);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_10, 0, x_58);
if (lean_is_scalar(x_12)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_12;
}
lean_ctor_set(x_59, 0, x_10);
lean_ctor_set(x_59, 1, x_11);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
x_62 = l_Lean_Syntax_getKind(x_60);
x_63 = lean_name_eq(x_1, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = l_Lean_Core_getTraceState___rarg(x_7, x_11);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_93, sizeof(void*)*1);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = 0;
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_61);
x_64 = x_98;
x_65 = x_95;
goto block_91;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
x_100 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_101 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_100, x_6, x_7, x_99);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_61);
x_64 = x_104;
x_65 = x_103;
goto block_91;
}
block_91:
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_1);
x_68 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
if (lean_is_scalar(x_12)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_12;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_12);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = l_Lean_Name_toString___closed__1;
x_72 = l_Lean_Name_toStringWithSep___main(x_71, x_62);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__11;
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__14;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Name_toStringWithSep___main(x_71, x_1);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Core_getConstInfo___closed__5;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_86 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_85, x_84, x_2, x_70, x_4, x_5, x_6, x_7, x_65);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__8;
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_88;
 lean_ctor_set_tag(x_90, 1);
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_62);
lean_dec(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_61);
if (lean_is_scalar(x_12)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_12;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_11);
return x_107;
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Formatter_checkKind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_checkKind___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_Formatter_concatArgs(x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("foo");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
x_10 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___rarg), 9, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_concatArgs(x_16, x_4, x_14, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_Lean_FileMap_ofString(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Core_getEnv___rarg(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_String_splitAux___main___closed__1;
x_13 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_16);
x_18 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_19 = l_Lean_Parser_tokenFn(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_String_splitAux___main___closed__1;
x_24 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_inc(x_1);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
x_29 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_30 = l_Lean_Parser_tokenFn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_parseToken(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean_string_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_String_trimRight(x_1);
x_15 = lean_string_dec_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = l_String_trimLeft(x_1);
x_21 = lean_string_dec_eq(x_20, x_1);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_ctor_set(x_3, 1, x_12);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = l_Lean_PrettyPrinter_Formatter_push(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_1);
lean_ctor_set(x_3, 1, x_1);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_PrettyPrinter_Formatter_push(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_3);
x_26 = l_String_trimLeft(x_1);
x_27 = lean_string_dec_eq(x_26, x_1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_11);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_30 = l_Lean_PrettyPrinter_Formatter_push(x_29, x_2, x_28, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_1);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_31, 2, x_11);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = l_Lean_PrettyPrinter_Formatter_push(x_32, x_2, x_31, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_9);
x_34 = l_String_trimLeft(x_1);
lean_inc(x_2);
lean_inc(x_34);
x_35 = l_Lean_PrettyPrinter_Formatter_parseToken(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_34);
x_40 = lean_string_append(x_34, x_10);
lean_dec(x_10);
lean_inc(x_2);
x_41 = l_Lean_PrettyPrinter_Formatter_parseToken(x_40, x_2, x_39, x_4, x_5, x_6, x_7, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_45, 1);
lean_dec(x_50);
x_51 = lean_string_dec_eq(x_34, x_1);
lean_dec(x_34);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_ctor_set(x_45, 1, x_12);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_1);
x_53 = 0;
x_54 = l_Lean_Format_flatten___main___closed__1;
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_53);
x_56 = l_Lean_PrettyPrinter_Formatter_push(x_55, x_2, x_45, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_inc(x_1);
lean_ctor_set(x_45, 1, x_1);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_1);
x_58 = 0;
x_59 = l_Lean_Format_flatten___main___closed__1;
x_60 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_58);
x_61 = l_Lean_PrettyPrinter_Formatter_push(x_60, x_2, x_45, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
x_64 = lean_string_dec_eq(x_34, x_1);
lean_dec(x_34);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_12);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_1);
x_67 = 0;
x_68 = l_Lean_Format_flatten___main___closed__1;
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_67);
x_70 = l_Lean_PrettyPrinter_Formatter_push(x_69, x_2, x_65, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_1);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_1);
lean_ctor_set(x_71, 2, x_63);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_73 = 0;
x_74 = l_Lean_Format_flatten___main___closed__1;
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_73);
x_76 = l_Lean_PrettyPrinter_Formatter_push(x_75, x_2, x_71, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_76;
}
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_45);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_string_dec_eq(x_34, x_1);
lean_dec(x_34);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
lean_ctor_set(x_45, 1, x_12);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_1);
x_81 = l_Lean_PrettyPrinter_Formatter_push(x_80, x_2, x_45, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_1);
x_82 = lean_string_append(x_1, x_78);
lean_dec(x_78);
lean_ctor_set(x_45, 1, x_82);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_1);
x_84 = l_Lean_PrettyPrinter_Formatter_push(x_83, x_2, x_45, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_45, 0);
x_86 = lean_ctor_get(x_45, 1);
x_87 = lean_ctor_get(x_45, 2);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_45);
x_88 = lean_string_dec_eq(x_34, x_1);
lean_dec(x_34);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_86);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_12);
lean_ctor_set(x_89, 2, x_87);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_1);
x_91 = l_Lean_PrettyPrinter_Formatter_push(x_90, x_2, x_89, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_inc(x_1);
x_92 = lean_string_append(x_1, x_86);
lean_dec(x_86);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_87);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_1);
x_95 = l_Lean_PrettyPrinter_Formatter_push(x_94, x_2, x_93, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_2);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_10);
x_96 = !lean_is_exclusive(x_3);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_3, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_3, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_3, 0);
lean_dec(x_99);
x_100 = l_String_trimLeft(x_1);
x_101 = lean_string_dec_eq(x_100, x_1);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_ctor_set(x_3, 1, x_12);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_1);
x_103 = l_Lean_PrettyPrinter_Formatter_push(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_inc(x_1);
lean_ctor_set(x_3, 1, x_1);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_1);
x_105 = l_Lean_PrettyPrinter_Formatter_push(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_105;
}
}
else
{
lean_object* x_106; uint8_t x_107; 
lean_dec(x_3);
x_106 = l_String_trimLeft(x_1);
x_107 = lean_string_dec_eq(x_106, x_1);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_9);
lean_ctor_set(x_108, 1, x_12);
lean_ctor_set(x_108, 2, x_11);
x_109 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_109, 0, x_1);
x_110 = l_Lean_PrettyPrinter_Formatter_push(x_109, x_2, x_108, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_1);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_9);
lean_ctor_set(x_111, 1, x_1);
lean_ctor_set(x_111, 2, x_11);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_1);
x_113 = l_Lean_PrettyPrinter_Formatter_push(x_112, x_2, x_111, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_113;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_12, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoWs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoWs_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_symbolNoWs_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not an atom: ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = 0;
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_formatStxAux___main(x_32, x_33, x_34, x_14);
x_36 = l_Lean_Options_empty;
x_37 = l_Lean_Format_pretty(x_35, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_12);
return x_44;
}
case 2:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_13);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_dec(x_14);
x_46 = l_String_trim(x_1);
x_47 = lean_string_dec_eq(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_48 = l_Lean_PrettyPrinter_Formatter_pushToken(x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_12);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_51, x_5, x_6, x_7, x_8, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_53 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_3, x_15, x_5, x_6, x_7, x_8, x_12);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_56, x_5, x_6, x_7, x_8, x_55);
return x_57;
}
}
default: 
{
lean_object* x_58; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_16 = x_58;
goto block_31;
}
}
block_31:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_formatStxAux___main(x_17, x_18, x_19, x_14);
x_21 = l_Lean_Options_empty;
x_22 = l_Lean_Format_pretty(x_20, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (lean_is_scalar(x_13)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_13;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
return x_30;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Syntax_structEq___main(x_10, x_11);
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
lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unimplemented: escaping non-atomic identifiers (is anyone even using those?)");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(303u);
x_3 = lean_unsigned_to_nat(35u);
x_4 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("«");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("»");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_identKind;
x_9 = l_Lean_PrettyPrinter_Formatter_checkKind(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Syntax_getId(x_16);
x_19 = l_Lean_Name_toString___closed__1;
lean_inc(x_18);
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_18);
lean_inc(x_1);
lean_inc(x_20);
x_21 = l_Lean_PrettyPrinter_Formatter_parseToken(x_20, x_1, x_17, x_3, x_4, x_5, x_6, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_55 = lean_ctor_get(x_24, 0);
lean_inc(x_55);
x_56 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_16);
x_57 = lean_array_push(x_56, x_16);
x_58 = lean_array_get_size(x_55);
x_59 = lean_array_get_size(x_57);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_16);
x_61 = lean_box(0);
x_26 = x_61;
goto block_54;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_isEqvAux___main___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(x_16, x_24, lean_box(0), x_55, x_57, x_62);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_24);
lean_dec(x_16);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_20);
x_64 = lean_box(0);
x_26 = x_64;
goto block_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_18);
x_65 = l_Lean_PrettyPrinter_Formatter_pushToken(x_20, x_1, x_25, x_3, x_4, x_5, x_6, x_23);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_68, x_3, x_4, x_5, x_6, x_67);
return x_69;
}
}
block_54:
{
lean_dec(x_26);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_PrettyPrinter_Formatter_pushToken(x_32, x_1, x_25, x_3, x_4, x_5, x_6, x_23);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_36, x_3, x_4, x_5, x_6, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
lean_dec(x_18);
x_38 = l_String_Inhabited;
x_39 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
x_40 = lean_panic_fn(x_38, x_39);
x_41 = l_Lean_PrettyPrinter_Formatter_pushToken(x_40, x_1, x_25, x_3, x_4, x_5, x_6, x_23);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_44, x_3, x_4, x_5, x_6, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_18);
x_46 = l_String_Inhabited;
x_47 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
x_48 = lean_panic_fn(x_46, x_47);
x_49 = l_Lean_PrettyPrinter_Formatter_pushToken(x_48, x_1, x_25, x_3, x_4, x_5, x_6, x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_52, x_3, x_4, x_5, x_6, x_51);
return x_53;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_9);
if (x_70 == 0)
{
return x_9;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_9, 0);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_9);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_identKind;
x_9 = l_Lean_PrettyPrinter_Formatter_checkKind(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Syntax_getId(x_16);
lean_dec(x_16);
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_18);
x_21 = l_Lean_PrettyPrinter_Formatter_pushToken(x_20, x_1, x_17, x_3, x_4, x_5, x_6, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_24, x_3, x_4, x_5, x_6, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_identEq_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = lean_name_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_12)) {
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
x_21 = l_Lean_Syntax_inhabited;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_20, x_22);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
x_41 = l_Lean_PrettyPrinter_Formatter_pushToken(x_40, x_2, x_19, x_4, x_5, x_6, x_7, x_18);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_44, x_4, x_5, x_6, x_7, x_43);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_2);
x_46 = lean_box(0);
x_24 = x_46;
goto block_39;
}
block_39:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = 0;
x_27 = l_Lean_Syntax_formatStxAux___main(x_25, x_26, x_22, x_12);
x_28 = l_Lean_Options_empty;
x_29 = l_Lean_Format_pretty(x_27, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_throwError___rarg(x_33, x_4, x_5, x_6, x_7, x_18);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_dec(x_17);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_dec(x_12);
x_50 = l_Lean_PrettyPrinter_Formatter_pushToken(x_49, x_2, x_48, x_4, x_5, x_6, x_7, x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_53, x_4, x_5, x_6, x_7, x_52);
return x_54;
}
default: 
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_17);
lean_dec(x_2);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_dec(x_16);
x_56 = lean_box(0);
x_57 = 0;
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Syntax_formatStxAux___main(x_56, x_57, x_58, x_12);
x_60 = l_Lean_Options_empty;
x_61 = l_Lean_Format_pretty(x_59, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Meta_throwError___rarg(x_65, x_4, x_5, x_6, x_7, x_55);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_12);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_16);
if (x_71 == 0)
{
return x_16;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_16, 0);
x_73 = lean_ctor_get(x_16, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_16);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_dec(x_1);
switch (lean_obj_tag(x_12)) {
case 1:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
x_76 = l_Lean_Syntax_inhabited;
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_get(x_76, x_75, x_77);
lean_dec(x_75);
if (lean_obj_tag(x_78) == 2)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_12);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_dec(x_78);
x_96 = l_Lean_PrettyPrinter_Formatter_pushToken(x_95, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_99, x_4, x_5, x_6, x_7, x_98);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec(x_78);
lean_dec(x_13);
lean_dec(x_2);
x_101 = lean_box(0);
x_79 = x_101;
goto block_94;
}
block_94:
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_79);
x_80 = lean_box(0);
x_81 = 0;
x_82 = l_Lean_Syntax_formatStxAux___main(x_80, x_81, x_77, x_12);
x_83 = l_Lean_Options_empty;
x_84 = l_Lean_Format_pretty(x_82, x_83);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_88 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Meta_throwError___rarg(x_88, x_4, x_5, x_6, x_7, x_11);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
case 2:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_12, 1);
lean_inc(x_102);
lean_dec(x_12);
x_103 = l_Lean_PrettyPrinter_Formatter_pushToken(x_102, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_106, x_4, x_5, x_6, x_7, x_105);
return x_107;
}
default: 
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_13);
lean_dec(x_2);
x_108 = lean_box(0);
x_109 = 0;
x_110 = lean_unsigned_to_nat(0u);
x_111 = l_Lean_Syntax_formatStxAux___main(x_108, x_109, x_110, x_12);
x_112 = l_Lean_Options_empty;
x_113 = l_Lean_Format_pretty(x_111, x_112);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Meta_throwError___rarg(x_117, x_4, x_5, x_6, x_7, x_11);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_charLitKind;
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_strLitKind;
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_nameLitKind;
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_fieldIdxKind;
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_15 = lean_apply_7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_3 = x_14;
x_5 = x_18;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_many_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed), 10, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_concatArgs(x_16, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
return x_17;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forMAux___main___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_many1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Syntax_getKind(x_12);
x_15 = l_Lean_nullKind;
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_apply_7(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_PrettyPrinter_Formatter_many_formatter(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_11);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_optional_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_concatArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_mod(x_14, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_20 = lean_apply_7(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_3 = x_15;
x_5 = x_23;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_29 = lean_apply_7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_3 = x_15;
x_5 = x_32;
x_10 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = l_List_range(x_16);
x_18 = l_List_reverse___rarg(x_17);
x_19 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed), 10, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Formatter_concatArgs(x_19, x_3, x_14, x_5, x_6, x_7, x_8, x_12);
return x_20;
}
}
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___main___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_sepBy_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_10 = lean_apply_8(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg), 8, 0);
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
lean_object* l_Lean_PrettyPrinter_Formatter_toggleInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = l_String_splitAux___main___closed__1;
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_Format_flatten___main___closed__1;
x_12 = l_Lean_PrettyPrinter_Formatter_push(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = l_String_splitAux___main___closed__1;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_14);
x_17 = l_Lean_Format_flatten___main___closed__1;
x_18 = l_Lean_PrettyPrinter_Formatter_push(x_17, x_1, x_16, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_3);
x_15 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_14, x_3, x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Formatter_push(x_1, x_3, x_18, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_22, x_5, x_6, x_7, x_8, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatDataValue___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_push___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatDataValue___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___lambda__1___boxed), 9, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_quotedSymbolKind;
x_9 = l_Lean_PrettyPrinter_Formatter_checkKind(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__3;
x_14 = l_Lean_PrettyPrinter_Formatter_concatArgs(x_13, x_1, x_12, x_3, x_4, x_5, x_6, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unquotedSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_unquotedSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_unquotedSymbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_7(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed), 10, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_PrettyPrinter_Formatter_ite___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_format(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Syntax_Traverser_fromSyntax(x_3);
x_10 = l_String_splitAux___main___closed__1;
x_11 = l_Array_empty___closed__1;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get_uint8(x_14, 5);
x_17 = 1;
x_18 = l_Lean_Meta_TransparencyMode_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_apply_7(x_2, x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Format_Inhabited;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_23, x_25);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Format_Inhabited;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get(x_31, x_30, x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_ctor_set_uint8(x_14, 5, x_17);
x_39 = lean_apply_7(x_2, x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Format_Inhabited;
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get(x_44, x_43, x_45);
lean_dec(x_43);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Format_Inhabited;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_get(x_51, x_50, x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; 
x_59 = lean_ctor_get_uint8(x_14, 0);
x_60 = lean_ctor_get_uint8(x_14, 1);
x_61 = lean_ctor_get_uint8(x_14, 2);
x_62 = lean_ctor_get_uint8(x_14, 3);
x_63 = lean_ctor_get_uint8(x_14, 4);
x_64 = lean_ctor_get_uint8(x_14, 5);
lean_dec(x_14);
x_65 = 1;
x_66 = l_Lean_Meta_TransparencyMode_lt(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_67, 0, x_59);
lean_ctor_set_uint8(x_67, 1, x_60);
lean_ctor_set_uint8(x_67, 2, x_61);
lean_ctor_set_uint8(x_67, 3, x_62);
lean_ctor_set_uint8(x_67, 4, x_63);
lean_ctor_set_uint8(x_67, 5, x_64);
lean_ctor_set(x_4, 0, x_67);
x_68 = lean_apply_7(x_2, x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Format_Inhabited;
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_get(x_74, x_73, x_75);
lean_dec(x_73);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_80 = x_68;
} else {
 lean_dec_ref(x_68);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_82, 0, x_59);
lean_ctor_set_uint8(x_82, 1, x_60);
lean_ctor_set_uint8(x_82, 2, x_61);
lean_ctor_set_uint8(x_82, 3, x_62);
lean_ctor_set_uint8(x_82, 4, x_63);
lean_ctor_set_uint8(x_82, 5, x_65);
lean_ctor_set(x_4, 0, x_82);
x_83 = lean_apply_7(x_2, x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_87, 2);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Format_Inhabited;
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_array_get(x_89, x_88, x_90);
lean_dec(x_88);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_85);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_83, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_95 = x_83;
} else {
 lean_dec_ref(x_83);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_97 = lean_ctor_get(x_4, 0);
x_98 = lean_ctor_get(x_4, 1);
x_99 = lean_ctor_get(x_4, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_4);
x_100 = lean_ctor_get_uint8(x_97, 0);
x_101 = lean_ctor_get_uint8(x_97, 1);
x_102 = lean_ctor_get_uint8(x_97, 2);
x_103 = lean_ctor_get_uint8(x_97, 3);
x_104 = lean_ctor_get_uint8(x_97, 4);
x_105 = lean_ctor_get_uint8(x_97, 5);
if (lean_is_exclusive(x_97)) {
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
 x_106 = lean_box(0);
}
x_107 = 1;
x_108 = l_Lean_Meta_TransparencyMode_lt(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 0, 6);
} else {
 x_109 = x_106;
}
lean_ctor_set_uint8(x_109, 0, x_100);
lean_ctor_set_uint8(x_109, 1, x_101);
lean_ctor_set_uint8(x_109, 2, x_102);
lean_ctor_set_uint8(x_109, 3, x_103);
lean_ctor_set_uint8(x_109, 4, x_104);
lean_ctor_set_uint8(x_109, 5, x_105);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_98);
lean_ctor_set(x_110, 2, x_99);
x_111 = lean_apply_7(x_2, x_1, x_12, x_110, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_115, 2);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l_Lean_Format_Inhabited;
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_array_get(x_117, x_116, x_118);
lean_dec(x_116);
if (lean_is_scalar(x_114)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_114;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_111, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_111, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_123 = x_111;
} else {
 lean_dec_ref(x_111);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
if (lean_is_scalar(x_106)) {
 x_125 = lean_alloc_ctor(0, 0, 6);
} else {
 x_125 = x_106;
}
lean_ctor_set_uint8(x_125, 0, x_100);
lean_ctor_set_uint8(x_125, 1, x_101);
lean_ctor_set_uint8(x_125, 2, x_102);
lean_ctor_set_uint8(x_125, 3, x_103);
lean_ctor_set_uint8(x_125, 4, x_104);
lean_ctor_set_uint8(x_125, 5, x_107);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_98);
lean_ctor_set(x_126, 2, x_99);
x_127 = lean_apply_7(x_2, x_1, x_12, x_126, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Format_Inhabited;
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_array_get(x_133, x_132, x_134);
lean_dec(x_132);
if (lean_is_scalar(x_130)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_130;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_129);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_127, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_139 = x_127;
} else {
 lean_dec_ref(x_127);
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
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_termParser___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_formatTerm___closed__1;
x_9 = l_Lean_PrettyPrinter_format(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_formatCommand___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_formatCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_formatCommand___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_formatCommand___closed__3;
x_9 = l_Lean_PrettyPrinter_format(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_PrettyPrinter_Formatter_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter_Formatter(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
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
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3);
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
l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_formatterAttribute___spec__1);
l_Lean_PrettyPrinter_formatterAttribute___closed__1 = _init_l_Lean_PrettyPrinter_formatterAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute___closed__1);
l_Lean_PrettyPrinter_formatterAttribute___closed__2 = _init_l_Lean_PrettyPrinter_formatterAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute___closed__2);
l_Lean_PrettyPrinter_formatterAttribute___closed__3 = _init_l_Lean_PrettyPrinter_formatterAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute___closed__3);
l_Lean_PrettyPrinter_formatterAttribute___closed__4 = _init_l_Lean_PrettyPrinter_formatterAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute___closed__4);
l_Lean_PrettyPrinter_formatterAttribute___closed__5 = _init_l_Lean_PrettyPrinter_formatterAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute___closed__5);
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
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__1);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__2);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__3);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__4);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__5);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__6);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser___closed__7);
l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser = _init_l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_FormatterM_monadTraverser);
l_Lean_PrettyPrinter_Formatter_concat___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_concat___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_concat___closed__1);
l_Lean_PrettyPrinter_Formatter_concat___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_concat___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_concat___closed__2);
l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__1);
l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__2);
l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKind___closed__3);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__2);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1___closed__3);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__4);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___closed__5);
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
l_Lean_PrettyPrinter_Formatter_checkKind___closed__9 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__9);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__10 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__10);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__11 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__11);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__12 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__12);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__13 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__13);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__14 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__14);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__1);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4);
l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_quotedSymbol_formatter___closed__3);
l_Lean_PrettyPrinter_formatTerm___closed__1 = _init_l_Lean_PrettyPrinter_formatTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTerm___closed__1);
l_Lean_PrettyPrinter_formatCommand___closed__1 = _init_l_Lean_PrettyPrinter_formatCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__1);
l_Lean_PrettyPrinter_formatCommand___closed__2 = _init_l_Lean_PrettyPrinter_formatCommand___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__2);
l_Lean_PrettyPrinter_formatCommand___closed__3 = _init_l_Lean_PrettyPrinter_formatCommand___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__3);
res = l___private_Lean_PrettyPrinter_Formatter_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
