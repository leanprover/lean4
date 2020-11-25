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
lean_object* l_Lean_PrettyPrinter_Formatter_State_stack___default;
extern lean_object* l_Lean_Parser_builtinTokenTable;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__9;
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460_(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2393_(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__29;
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__11;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__53;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__10;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__42;
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_7791____closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__37;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__55;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__8;
extern lean_object* l_Lean_identKind___closed__1;
extern lean_object* l_Lean_Parser_Tactic_generalize___closed__6;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___rarg(lean_object*);
lean_object* l_Lean_Parser_getBinaryAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_7535____closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Notation___hyg_3____closed__13;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_format_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__21;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__38;
lean_object* l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__10;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__51;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg(lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__29;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__19;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3894____closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__44;
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_format___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__10;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterFormatterAliasValue(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1;
lean_object* l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__47;
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instCoeArrowFormatterFormatterFormatterAliasValue(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4;
extern lean_object* l_Lean_nameLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__46;
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__16;
lean_object* l_Lean_PrettyPrinter_Formatter_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter_match__1(lean_object*);
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(lean_object*);
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__12;
lean_object* l_String_trimRight(lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__14;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__28;
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParserOfStack_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__5;
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__18;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__30;
lean_object* l_IO_mkRef___at_IO_FS_withIsolatedStreams___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__23;
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_contains(lean_object*, uint32_t);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__13;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__41;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
extern lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__52;
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_toggleInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_instInhabitedKeyedDeclsAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__54;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter___rarg(lean_object*);
lean_object* l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__33;
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__22;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_format___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_withoutForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_location___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__24;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__8;
lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instCoeArrowFormatterArrowFormatterFormatterFormatterAliasValue(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__49;
extern lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq___closed__4;
lean_object* l_Lean_PrettyPrinter_formatterAttribute;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter_match__1(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__26;
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__5;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__14;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
uint8_t l_Substring_beq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__39;
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_inaccessible_user_name(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__35;
lean_object* l_String_trimLeft(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setExpected_formatter(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__7;
lean_object* l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_instReprIterator___closed__2;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object*, lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__36;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Notation___hyg_6289____closed__5;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_State_leadWord___default;
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__43;
lean_object* l_Lean_PrettyPrinter_Formatter_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM_match__1___rarg(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1;
lean_object* l_Lean_Parser_getConstAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_FormatterM_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__15;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__3;
lean_object* l_Lean_Parser_getUnaryAlias___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_FormatterM_orelse(lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_7979____closed__4;
lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_7663____closed__4;
extern lean_object* l___kind_term____x40_Init_Notation___hyg_7049____closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__56;
lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__2;
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___boxed(lean_object*);
extern lean_object* l_Lean_ParserCompiler_CombinatorAttribute_instInhabitedCombinatorAttribute___closed__1;
extern lean_object* l_Lean_Format_getWidth___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*);
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_38____closed__2;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__10;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__32;
uint8_t l_Lean_Name_isNum(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__20;
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3;
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__53;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withForbidden_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_many_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object*);
extern lean_object* l_Int_instInhabitedInt___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__7;
extern lean_object* l_Lean_Name_toStringWithSep___closed__1;
lean_object* l_Lean_Format_getIndent(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedByCategoryToken_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__12;
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_format_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__25;
lean_object* l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_instInhabitedFormat;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_PrettyPrinter_Formatter_indent___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__57;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__17;
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_pushTokenCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__8;
extern lean_object* l_Array___kind_term____x40_Init_Data_Array_Subarray___hyg_510____closed__13;
lean_object* l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__34;
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__48;
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_7407____closed__8;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_3026_(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__50;
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1;
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
extern lean_object* l_Array_instReprArray___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkOutsideQuot_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__1(lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__11;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_visitAtom___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp_macro_scopes(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2;
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__17;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__8;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_inductionAlts___closed__8;
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l___kind_term____x40_Init_Notation___hyg_3____closed__16;
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__11;
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
lean_object* l_Lean_PrettyPrinter_Formatter_suppressInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_visitAtom___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_checkInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__31;
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm___closed__1;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_forM___at_Lean_PrettyPrinter_Formatter_sepBy_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
lean_object* l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2;
extern lean_object* l_instReprChar___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM_match__1(lean_object*, lean_object*);
extern lean_object* l_Lean_interpolatedStrLitKind;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_pushTokenCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__45;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__9;
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Lean_PrettyPrinter_Formatter_pushTokenCore___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__40;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__27;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___closed__7;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_State_leadWord___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
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
static lean_object* _init_l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_FormatterM_orelse___rarg), 7, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1;
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
x_1 = l_instReprChar___closed__1;
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
x_14 = l_Lean_throwError___at_Lean_addAttribute___spec__2(x_13, lean_box(0), x_3, x_4, x_5, x_9);
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
x_18 = l_Lean_Name_toString___closed__1;
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
x_26 = l_Lean_throwError___at_Lean_addAttribute___spec__2(x_25, lean_box(0), x_3, x_4, x_5, x_9);
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
x_1 = l_myMacro____x40_Init_Notation___hyg_38____closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
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
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__2___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3;
x_2 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4;
x_2 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__5;
x_3 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__7;
return x_1;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_StateRefT_x27_get___at_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_24 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_5 = l_Lean_Format_instInhabitedFormat;
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
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Syntax_getKind(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4;
x_2 = l_Lean_Format_getWidth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("formatting ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_23; lean_object* x_24; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_st_ref_get(x_6, x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_23 = x_44;
x_24 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5;
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(x_46, x_3, x_4, x_5, x_6, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox(x_48);
lean_dec(x_48);
x_23 = x_50;
x_24 = x_49;
goto block_38;
}
block_22:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Syntax_getKind(x_2);
x_10 = l_Lean_choiceKind___closed__2;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Name_toString___closed__1;
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
x_19 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_17, x_18, x_3, x_4, x_5, x_6, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_1);
x_20 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__3;
x_21 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_20, x_3, x_4, x_5, x_6, x_8);
return x_21;
}
}
block_38:
{
if (x_23 == 0)
{
x_8 = x_24;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_2);
x_25 = l_Lean_fmt___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofList___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__7;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5;
x_36 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_35, x_34, x_3, x_4, x_5, x_6, x_24);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_8 = x_37;
goto block_22;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_indent___boxed), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_group(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Formatter_atomic_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("backtrack");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5;
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected node kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected '");
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
x_37 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(x_37, x_2, x_3, x_4, x_5, x_36);
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
x_17 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
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
x_25 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_26 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_25, x_24, x_2, x_3, x_4, x_5, x_14);
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
x_71 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_72 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(x_71, x_2, x_3, x_4, x_5, x_70);
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
x_51 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
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
x_59 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_60 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_59, x_58, x_2, x_3, x_4, x_5, x_48);
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
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__1___rarg), 7, 2);
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
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_24 = l_Lean_instInhabitedParserDescr___closed__1;
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
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = l_Lean_instInhabitedParserDescr___closed__1;
lean_ctor_set(x_8, 1, x_12);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_instInhabitedParserDescr___closed__1;
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_st_ref_set(x_3, x_23, x_9);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_14, x_16, x_15);
lean_inc(x_16);
x_18 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_14, x_17, x_16);
x_19 = lean_nat_sub(x_18, x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1;
lean_inc(x_18);
lean_inc(x_14);
lean_ctor_set(x_12, 1, x_18);
x_23 = 10;
x_24 = l_Substring_contains(x_12, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_8);
x_25 = lean_string_utf8_extract(x_14, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
x_26 = l_Lean_instInhabitedParserDescr___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_instReprIterator___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_PrettyPrinter_Formatter_push(x_30, x_3, x_4, x_5, x_6, x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_22, x_32, x_3, x_4, x_5, x_6, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = l_Lean_Format_getIndent(x_35);
lean_dec(x_35);
x_37 = lean_nat_to_int(x_36);
x_38 = l_Int_instInhabitedInt___closed__1;
x_39 = lean_int_sub(x_38, x_37);
lean_dec(x_37);
lean_ctor_set(x_8, 0, x_39);
x_40 = lean_string_utf8_extract(x_14, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
x_41 = l_Lean_instInhabitedParserDescr___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_push___boxed), 6, 1);
lean_closure_set(x_46, 0, x_45);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_PrettyPrinter_Formatter_indent(x_46, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_apply_6(x_22, x_48, x_3, x_4, x_5, x_6, x_49);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
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
lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
lean_dec(x_17);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
x_59 = lean_ctor_get(x_12, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_60 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_57, x_59, x_58);
lean_inc(x_59);
x_61 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_57, x_60, x_59);
x_62 = lean_nat_sub(x_61, x_60);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_eq(x_62, x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint32_t x_67; uint8_t x_68; 
x_65 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1;
lean_inc(x_61);
lean_inc(x_57);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_59);
x_67 = 10;
x_68 = l_Substring_contains(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_8);
x_69 = lean_string_utf8_extract(x_57, x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_57);
x_70 = l_Lean_instInhabitedParserDescr___closed__1;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_instReprIterator___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_PrettyPrinter_Formatter_push(x_74, x_3, x_4, x_5, x_6, x_7);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_apply_6(x_65, x_76, x_3, x_4, x_5, x_6, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
x_80 = l_Lean_Format_getIndent(x_79);
lean_dec(x_79);
x_81 = lean_nat_to_int(x_80);
x_82 = l_Int_instInhabitedInt___closed__1;
x_83 = lean_int_sub(x_82, x_81);
lean_dec(x_81);
lean_ctor_set(x_8, 0, x_83);
x_84 = lean_string_utf8_extract(x_57, x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_57);
x_85 = l_Lean_instInhabitedParserDescr___closed__1;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_push___boxed), 6, 1);
lean_closure_set(x_90, 0, x_89);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l_Lean_PrettyPrinter_Formatter_indent(x_90, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_apply_6(x_65, x_92, x_3, x_4, x_5, x_6, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_97 = x_91;
} else {
 lean_dec_ref(x_91);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_101 = lean_ctor_get(x_8, 0);
lean_inc(x_101);
lean_dec(x_8);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 2);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
x_106 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_102, x_104, x_103);
lean_inc(x_104);
x_107 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_102, x_106, x_104);
x_108 = lean_nat_sub(x_107, x_106);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_dec_eq(x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint32_t x_113; uint8_t x_114; 
x_111 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1;
lean_inc(x_107);
lean_inc(x_102);
if (lean_is_scalar(x_105)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_105;
}
lean_ctor_set(x_112, 0, x_102);
lean_ctor_set(x_112, 1, x_107);
lean_ctor_set(x_112, 2, x_104);
x_113 = 10;
x_114 = l_Substring_contains(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_string_utf8_extract(x_102, x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_102);
x_116 = l_Lean_instInhabitedParserDescr___closed__1;
x_117 = lean_string_append(x_116, x_115);
lean_dec(x_115);
x_118 = l_instReprIterator___closed__2;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_PrettyPrinter_Formatter_push(x_120, x_3, x_4, x_5, x_6, x_7);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_apply_6(x_111, x_122, x_3, x_4, x_5, x_6, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_125 = lean_ctor_get(x_5, 0);
lean_inc(x_125);
x_126 = l_Lean_Format_getIndent(x_125);
lean_dec(x_125);
x_127 = lean_nat_to_int(x_126);
x_128 = l_Int_instInhabitedInt___closed__1;
x_129 = lean_int_sub(x_128, x_127);
lean_dec(x_127);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_string_utf8_extract(x_102, x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_102);
x_132 = l_Lean_instInhabitedParserDescr___closed__1;
x_133 = lean_string_append(x_132, x_131);
lean_dec(x_131);
x_134 = l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
x_135 = lean_string_append(x_133, x_134);
x_136 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_push___boxed), 6, 1);
lean_closure_set(x_137, 0, x_136);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_138 = l_Lean_PrettyPrinter_Formatter_indent(x_137, x_130, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_130);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_apply_6(x_111, x_139, x_3, x_4, x_5, x_6, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_7);
return x_147;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_dec(x_10);
x_48 = l_Lean_instInhabitedParserDescr___closed__1;
x_49 = lean_string_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_String_trimRight(x_2);
x_51 = lean_string_dec_eq(x_50, x_2);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = lean_box(0);
x_12 = x_52;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = l_String_trimLeft(x_2);
lean_inc(x_53);
x_54 = lean_string_append(x_53, x_47);
lean_dec(x_47);
x_55 = l_Lean_PrettyPrinter_Formatter_parseToken(x_54, x_4, x_5, x_6, x_7, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_string_utf8_byte_size(x_53);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_61 = l_instReprIterator___closed__2;
lean_inc(x_2);
x_62 = lean_string_append(x_2, x_61);
x_63 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_62, x_4, x_5, x_6, x_7, x_57);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_take(x_5, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_dec(x_69);
x_70 = lean_string_dec_eq(x_53, x_2);
lean_dec(x_53);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
lean_ctor_set(x_66, 1, x_48);
x_71 = lean_st_ref_set(x_5, x_66, x_67);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_73, x_4, x_5, x_6, x_7, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_ctor_set(x_66, 1, x_2);
x_75 = lean_st_ref_set(x_5, x_66, x_67);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_77, x_4, x_5, x_6, x_7, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_66, 0);
x_80 = lean_ctor_get(x_66, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_string_dec_eq(x_53, x_2);
lean_dec(x_53);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_48);
lean_ctor_set(x_82, 2, x_80);
x_83 = lean_st_ref_set(x_5, x_82, x_67);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_box(0);
x_86 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_85, x_4, x_5, x_6, x_7, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_80);
x_88 = lean_st_ref_set(x_5, x_87, x_67);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_box(0);
x_91 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_90, x_4, x_5, x_6, x_7, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_inc(x_2);
x_92 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_2, x_4, x_5, x_6, x_7, x_57);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_st_ref_take(x_5, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_string_dec_eq(x_53, x_2);
lean_dec(x_53);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_98);
lean_dec(x_2);
lean_ctor_set(x_95, 1, x_48);
x_100 = lean_st_ref_set(x_5, x_95, x_96);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_102, x_4, x_5, x_6, x_7, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_string_append(x_2, x_98);
lean_dec(x_98);
lean_ctor_set(x_95, 1, x_104);
x_105 = lean_st_ref_set(x_5, x_95, x_96);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_box(0);
x_108 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_107, x_4, x_5, x_6, x_7, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_95, 0);
x_110 = lean_ctor_get(x_95, 1);
x_111 = lean_ctor_get(x_95, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_95);
x_112 = lean_string_dec_eq(x_53, x_2);
lean_dec(x_53);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_110);
lean_dec(x_2);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_48);
lean_ctor_set(x_113, 2, x_111);
x_114 = lean_st_ref_set(x_5, x_113, x_96);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_box(0);
x_117 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_116, x_4, x_5, x_6, x_7, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_string_append(x_2, x_110);
lean_dec(x_110);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_111);
x_120 = lean_st_ref_set(x_5, x_119, x_96);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_122, x_4, x_5, x_6, x_7, x_121);
return x_123;
}
}
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_47);
x_124 = lean_box(0);
x_12 = x_124;
goto block_46;
}
block_46:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
lean_inc(x_2);
x_13 = l_Lean_PrettyPrinter_Formatter_pushTokenCore(x_2, x_4, x_5, x_6, x_7, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
x_20 = l_String_trimLeft(x_2);
x_21 = lean_string_dec_eq(x_20, x_2);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_22 = l_Lean_instInhabitedParserDescr___closed__1;
lean_ctor_set(x_16, 1, x_22);
x_23 = lean_st_ref_set(x_5, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_25, x_4, x_5, x_6, x_7, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_ctor_set(x_16, 1, x_2);
x_27 = lean_st_ref_set(x_5, x_16, x_17);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_29, x_4, x_5, x_6, x_7, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = l_String_trimLeft(x_2);
x_34 = lean_string_dec_eq(x_33, x_2);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_35 = l_Lean_instInhabitedParserDescr___closed__1;
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_st_ref_set(x_5, x_36, x_17);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_39, x_4, x_5, x_6, x_7, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_32);
x_42 = lean_st_ref_set(x_5, x_41, x_17);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_44, x_4, x_5, x_6, x_7, x_43);
return x_45;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
lean_ctor_set(x_9, 1, x_13);
x_14 = lean_st_ref_set(x_4, x_9, x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_1, x_16, x_3, x_4, x_5, x_6, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l_Lean_instInhabitedParserDescr___closed__1;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
x_22 = lean_st_ref_set(x_4, x_21, x_10);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_6(x_1, x_24, x_3, x_4, x_5, x_6, x_23);
return x_25;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3___boxed), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 2);
x_17 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_14, x_16, x_15);
lean_inc(x_16);
x_18 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_14, x_17, x_16);
x_19 = lean_nat_sub(x_18, x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_18);
lean_inc(x_14);
lean_ctor_set(x_11, 1, x_18);
x_22 = 10;
x_23 = l_Substring_contains(x_11, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_string_utf8_extract(x_14, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_instInhabitedParserDescr___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_PrettyPrinter_Formatter_push(x_29, x_3, x_4, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_12, x_31, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_string_utf8_extract(x_14, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
x_35 = l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_instInhabitedParserDescr___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_PrettyPrinter_Formatter_push(x_39, x_3, x_4, x_5, x_6, x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_12, x_41, x_3, x_4, x_5, x_6, x_42);
lean_dec(x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_18);
lean_dec(x_17);
lean_free_object(x_11);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_44 = lean_box(0);
x_45 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_1, x_2, x_44, x_3, x_4, x_5, x_6, x_7);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
x_48 = lean_ctor_get(x_11, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_49 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_46, x_48, x_47);
lean_inc(x_48);
x_50 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_46, x_49, x_48);
x_51 = lean_nat_sub(x_50, x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; uint32_t x_55; uint8_t x_56; 
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_50);
lean_inc(x_46);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_48);
x_55 = 10;
x_56 = l_Substring_contains(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_string_utf8_extract(x_46, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_46);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___closed__3;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_instInhabitedParserDescr___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_PrettyPrinter_Formatter_push(x_62, x_3, x_4, x_5, x_6, x_7);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_12, x_64, x_3, x_4, x_5, x_6, x_65);
lean_dec(x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_string_utf8_extract(x_46, x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_46);
x_68 = l___private_Lean_Data_Format_0__Lean_Format_pushNewline___closed__1;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lean_instInhabitedParserDescr___closed__1;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_PrettyPrinter_Formatter_push(x_72, x_3, x_4, x_5, x_6, x_7);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_12, x_74, x_3, x_4, x_5, x_6, x_75);
lean_dec(x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_12);
x_77 = lean_box(0);
x_78 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_1, x_2, x_77, x_3, x_4, x_5, x_6, x_7);
return x_78;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Formatter_symbol_formatter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbol_formatter_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax '");
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
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected symbol '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__7;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Formatter.symbol.formatter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__9;
x_2 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__10;
x_3 = lean_unsigned_to_nat(290u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
uint8_t x_11; lean_object* x_12; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_st_ref_get(x_5, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_11 = x_34;
x_12 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_37 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__4(x_36, x_2, x_3, x_4, x_5, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_11 = x_40;
x_12 = x_39;
goto block_28;
}
block_28:
{
if (x_11 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = l_Lean_fmt___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__6;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_25 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__3(x_24, x_23, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_26);
return x_27;
}
}
}
else
{
if (lean_obj_tag(x_8) == 2)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_PrettyPrinter_Formatter_pushToken(x_41, x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_1);
x_49 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__8;
x_50 = l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__11;
x_51 = lean_panic_fn(x_49, x_50);
x_52 = lean_apply_5(x_51, x_2, x_3, x_4, x_5, x_9);
return x_52;
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3() {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3;
x_17 = l_String_trim(x_1);
x_18 = lean_string_dec_eq(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_PrettyPrinter_Formatter_pushToken(x_14, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_apply_6(x_16, x_20, x_3, x_4, x_5, x_6, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_PrettyPrinter_Formatter_pushToken(x_14, x_1, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_apply_6(x_16, x_28, x_3, x_4, x_5, x_6, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_9);
x_37 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(x_40, lean_box(0), x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter_match__1___rarg), 3, 0);
return x_2;
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
x_6 = l_Lean_Name_toString___closed__1;
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
x_15 = l_Lean_Name_toString___closed__1;
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
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not an ident: ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 3)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_simp_macro_scopes(x_16);
x_18 = l_Lean_Name_toString___closed__1;
lean_inc(x_17);
x_19 = l_Lean_Name_toStringWithSep(x_18, x_17);
x_20 = l_Lean_Name_isAnonymous(x_17);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc(x_17);
x_21 = lean_is_inaccessible_user_name(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_22 = l_Lean_Name_components(x_17);
x_23 = 0;
x_24 = l_List_foldr___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__1(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Array_instReprArray___rarg___closed__1;
x_26 = l_String_isPrefixOf(x_25, x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_19);
x_27 = l_Lean_PrettyPrinter_Formatter_parseToken(x_19, x_1, x_2, x_3, x_4, x_14);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_string_utf8_byte_size(x_19);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_19);
x_33 = l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2(x_22);
x_34 = lean_box(0);
x_35 = l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(x_34, x_33);
x_36 = l_Lean_Name_toStringWithSep(x_18, x_35);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_36, x_1, x_2, x_3, x_4, x_29);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_38);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_22);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_44 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_19, x_1, x_2, x_3, x_4, x_29);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_45);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_22);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_19, x_1, x_2, x_3, x_4, x_14);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_52);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_22);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_19, x_1, x_2, x_3, x_4, x_14);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_59);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_17);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_65 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_19, x_1, x_2, x_3, x_4, x_14);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_19);
lean_dec(x_17);
x_72 = l_Lean_Name_toStringWithSep___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_72, x_1, x_2, x_3, x_4, x_14);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_2, x_3, x_4, x_74);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_13);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_10);
x_82 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(x_85, lean_box(0), x_1, x_2, x_3, x_4, x_80);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_7);
if (x_87 == 0)
{
return x_7;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_7, 0);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_7);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
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
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdent_formatter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_rawIdent_formatter_match__1___rarg), 3, 0);
return x_2;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 3)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep(x_17, x_16);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_PrettyPrinter_Formatter_pushToken(x_15, x_18, x_1, x_2, x_3, x_4, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(x_2, x_3, x_4, x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_10);
x_28 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___spec__1(x_31, lean_box(0), x_1, x_2, x_3, x_4, x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
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
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg), 5, 0);
return x_2;
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
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_visitAtom___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = l_Lean_instInhabitedSyntax;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_PrettyPrinter_Formatter_pushToken(x_20, x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
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
lean_dec(x_19);
x_29 = lean_box(0);
x_8 = x_29;
goto block_15;
}
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_PrettyPrinter_Formatter_pushToken(x_30, x_31, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___rarg(x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
default: 
{
lean_object* x_39; 
x_39 = lean_box(0);
x_8 = x_39;
goto block_15;
}
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_visitAtom___spec__1(x_13, lean_box(0), x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_visitAtom___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_visitAtom___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_strLitKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_numLitKind;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
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
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_18 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_10 = l_Lean_instInhabitedParserDescr___closed__1;
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
x_20 = l_Lean_instInhabitedParserDescr___closed__1;
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
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
x_29 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_symbol_formatter___spec__1___rarg(x_7, x_8, x_9, x_28);
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
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2393_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___at_IO_FS_withIsolatedStreams___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterFormatterAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instCoeArrowFormatterFormatterFormatterAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_instCoeArrowFormatterArrowFormatterFormatterFormatterAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_numLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_numLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__5;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__6;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_strLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_strLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__10;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__11;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__12;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_charLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_charLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__15;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__16;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__17;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_nameLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__20;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__21;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__22;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_identKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_identKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__25;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 8, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__26;
x_2 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__27;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__28;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__30;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__32;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__34;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_atomic_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__36;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_many_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__38;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_many1_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__40;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__42;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_optional_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__44;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withPosition_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__46;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__48;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_sepBy_formatter), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__50;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_sepBy1_formatter), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__52;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__54;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__56;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_3 = l___kind_term____x40_Init_Notation___hyg_7049____closed__5;
x_4 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__2;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array___kind_term____x40_Init_Data_Array_Subarray___hyg_510____closed__13;
x_8 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__4;
x_9 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_7, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__8;
x_12 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__9;
x_13 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_11, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__11;
x_16 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__14;
x_17 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_15, x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__14;
x_20 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__19;
x_21 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_19, x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__17;
x_24 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__24;
x_25 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_23, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_identKind___closed__2;
x_28 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__29;
x_29 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_27, x_28, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Parser_Tactic_intro___closed__12;
x_32 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__31;
x_33 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_31, x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Parser_Tactic_inductionAlts___closed__10;
x_36 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__33;
x_37 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_35, x_36, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__29;
x_40 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__35;
x_41 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_39, x_40, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Parser_Tactic_generalize___closed__6;
x_44 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__37;
x_45 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_43, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_myMacro____x40_Init_Notation___hyg_7535____closed__4;
x_48 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__39;
x_49 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_47, x_48, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_myMacro____x40_Init_Notation___hyg_7407____closed__8;
x_52 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__41;
x_53 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_51, x_52, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_myMacro____x40_Init_Notation___hyg_7979____closed__4;
x_56 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__43;
x_57 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_55, x_56, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_7663____closed__4;
x_60 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__45;
x_61 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_59, x_60, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Parser_Tactic_location___closed__4;
x_64 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__47;
x_65 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_63, x_64, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__10;
x_68 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__49;
x_69 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_67, x_68, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l___kind_term____x40_Init_Notation___hyg_6289____closed__5;
x_72 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__51;
x_73 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_71, x_72, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Parser_Tactic_inductionAlts___closed__8;
x_76 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__53;
x_77 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_75, x_76, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_myMacro____x40_Init_Notation___hyg_7791____closed__6;
x_80 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__55;
x_81 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_79, x_80, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___kind_term____x40_Init_Notation___hyg_3____closed__13;
x_84 = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__57;
x_85 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_83, x_84, x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_1887____closed__53;
x_88 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_87, x_72, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Parser_Tactic_rwRuleSeq___closed__4;
x_91 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_90, x_76, x_89);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_85);
if (x_96 == 0)
{
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_85, 0);
x_98 = lean_ctor_get(x_85, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_85);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_81);
if (x_100 == 0)
{
return x_81;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_81, 0);
x_102 = lean_ctor_get(x_81, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_81);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_77);
if (x_104 == 0)
{
return x_77;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_77, 0);
x_106 = lean_ctor_get(x_77, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_77);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_73);
if (x_108 == 0)
{
return x_73;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_73, 0);
x_110 = lean_ctor_get(x_73, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_73);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_69);
if (x_112 == 0)
{
return x_69;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_69, 0);
x_114 = lean_ctor_get(x_69, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_69);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_65);
if (x_116 == 0)
{
return x_65;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_65, 0);
x_118 = lean_ctor_get(x_65, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_65);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_61);
if (x_120 == 0)
{
return x_61;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_61, 0);
x_122 = lean_ctor_get(x_61, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_61);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_57);
if (x_124 == 0)
{
return x_57;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_57, 0);
x_126 = lean_ctor_get(x_57, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_57);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_53);
if (x_128 == 0)
{
return x_53;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_53, 0);
x_130 = lean_ctor_get(x_53, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_53);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_49);
if (x_132 == 0)
{
return x_49;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_49, 0);
x_134 = lean_ctor_get(x_49, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_49);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_45);
if (x_136 == 0)
{
return x_45;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_45, 0);
x_138 = lean_ctor_get(x_45, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_45);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_41);
if (x_140 == 0)
{
return x_41;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_41, 0);
x_142 = lean_ctor_get(x_41, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_41);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_37);
if (x_144 == 0)
{
return x_37;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_37, 0);
x_146 = lean_ctor_get(x_37, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_37);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_33);
if (x_148 == 0)
{
return x_33;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_33, 0);
x_150 = lean_ctor_get(x_33, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_33);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_29);
if (x_152 == 0)
{
return x_29;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_29, 0);
x_154 = lean_ctor_get(x_29, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_29);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_25);
if (x_156 == 0)
{
return x_25;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_25, 0);
x_158 = lean_ctor_get(x_25, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_25);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_21);
if (x_160 == 0)
{
return x_21;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_21, 0);
x_162 = lean_ctor_get(x_21, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_21);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_17);
if (x_164 == 0)
{
return x_17;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_17, 0);
x_166 = lean_ctor_get(x_17, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_17);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_13);
if (x_168 == 0)
{
return x_13;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_13, 0);
x_170 = lean_ctor_get(x_13, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_13);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_9);
if (x_172 == 0)
{
return x_9;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_9, 0);
x_174 = lean_ctor_get(x_9, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_9);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_5);
if (x_176 == 0)
{
return x_5;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_5, 0);
x_178 = lean_ctor_get(x_5, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_5);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_3, x_14, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_3(x_4, x_17, x_18, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_3(x_5, x_21, x_22, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_apply_3(x_7, x_25, x_26, x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_1(x_8, x_29);
return x_30;
}
case 6:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_33 = lean_box(x_32);
x_34 = lean_apply_2(x_9, x_31, x_33);
return x_34;
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_apply_2(x_11, x_35, x_36);
return x_37;
}
case 8:
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_apply_1(x_10, x_38);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_apply_3(x_6, x_40, x_41, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr_match__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_8 = l_Lean_Parser_getConstAlias___rarg(x_7, x_5, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_io_error_to_string(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_io_error_to_string(x_19);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
x_29 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_30 = l_Lean_Parser_getUnaryAlias___rarg(x_29, x_26, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_pretty_printer_formatter_interpret_parser_descr(x_27, x_2, x_3, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_36, 0, x_31);
lean_closure_set(x_36, 1, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__1), 7, 2);
lean_closure_set(x_39, 0, x_31);
lean_closure_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_31);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_io_error_to_string(x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_30, 0, x_50);
return x_30;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_30, 0);
x_52 = lean_ctor_get(x_30, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_30);
x_53 = lean_io_error_to_string(x_51);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_ctor_get(x_2, 3);
lean_inc(x_61);
x_62 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_63 = l_Lean_Parser_getBinaryAlias___rarg(x_62, x_58, x_4);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_3);
lean_inc(x_2);
x_66 = lean_pretty_printer_formatter_interpret_parser_descr(x_59, x_2, x_3, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_pretty_printer_formatter_interpret_parser_descr(x_60, x_2, x_3, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2), 8, 3);
lean_closure_set(x_72, 0, x_64);
lean_closure_set(x_72, 1, x_67);
lean_closure_set(x_72, 2, x_71);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__2), 8, 3);
lean_closure_set(x_75, 0, x_64);
lean_closure_set(x_75, 1, x_67);
lean_closure_set(x_75, 2, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_67);
lean_dec(x_64);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_63);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_63, 0);
x_87 = lean_io_error_to_string(x_86);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_61);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_63, 0, x_90);
return x_63;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_63, 0);
x_92 = lean_ctor_get(x_63, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_63);
x_93 = lean_io_error_to_string(x_91);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_61);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
return x_97;
}
}
}
case 3:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 2);
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
x_103 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3), 7, 2);
lean_closure_set(x_103, 0, x_98);
lean_closure_set(x_103, 1, x_102);
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
x_106 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__3), 7, 2);
lean_closure_set(x_106, 0, x_98);
lean_closure_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_98);
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
case 4:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 2);
lean_inc(x_114);
lean_dec(x_1);
x_115 = lean_pretty_printer_formatter_interpret_parser_descr(x_114, x_2, x_3, x_4);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed), 8, 3);
lean_closure_set(x_118, 0, x_112);
lean_closure_set(x_118, 1, x_113);
lean_closure_set(x_118, 2, x_117);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
x_121 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed), 8, 3);
lean_closure_set(x_121, 0, x_112);
lean_closure_set(x_121, 1, x_113);
lean_closure_set(x_121, 2, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_113);
lean_dec(x_112);
x_123 = !lean_is_exclusive(x_115);
if (x_123 == 0)
{
return x_115;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_115, 0);
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_115);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
case 5:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
lean_dec(x_1);
x_128 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__5), 6, 1);
lean_closure_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_4);
return x_129;
}
case 6:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_3);
lean_dec(x_2);
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__6), 6, 1);
lean_closure_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_4);
return x_132;
}
case 7:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
lean_dec(x_1);
x_134 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__7), 6, 1);
lean_closure_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_4);
return x_135;
}
case 8:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
lean_dec(x_1);
x_137 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
x_138 = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___rarg(x_137, x_136, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_138;
}
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 2);
lean_inc(x_140);
lean_dec(x_1);
x_141 = lean_pretty_printer_formatter_interpret_parser_descr(x_140, x_2, x_3, x_4);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_144, 0, x_139);
lean_closure_set(x_144, 1, x_143);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_141, 0);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_141);
x_147 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__8), 7, 2);
lean_closure_set(x_147, 0, x_139);
lean_closure_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
uint8_t x_149; 
lean_dec(x_139);
x_149 = !lean_is_exclusive(x_141);
if (x_149 == 0)
{
return x_141;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_141, 0);
x_151 = lean_ctor_get(x_141, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_141);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___elambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
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
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_3, 3);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 3);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_8);
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Std_PersistentArray_push___rarg(x_17, x_19);
lean_ctor_set(x_12, 0, x_20);
x_21 = lean_st_ref_set(x_4, x_11, x_13);
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
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_8);
lean_inc(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_PersistentArray_push___rarg(x_29, x_31);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_28);
lean_ctor_set(x_11, 3, x_33);
x_34 = lean_st_ref_set(x_4, x_11, x_13);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
x_41 = lean_ctor_get(x_11, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_42 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_44 = x_12;
} else {
 lean_dec_ref(x_12);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_8);
lean_inc(x_6);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Std_PersistentArray_push___rarg(x_43, x_46);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_44;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_42);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_41);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_set(x_4, x_49, x_13);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_format___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_checkTraceOption(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
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
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("input");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5;
x_2 = l_Lean_PrettyPrinter_format___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_format(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_62; lean_object* x_63; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_st_ref_get(x_4, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = 0;
x_62 = x_78;
x_63 = x_77;
goto block_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
x_80 = l_Lean_PrettyPrinter_format___closed__5;
x_81 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_format___spec__2(x_80, x_3, x_4, x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_62 = x_84;
x_63 = x_83;
goto block_72;
}
block_61:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = l_Lean_Parser_builtinTokenTable;
x_9 = lean_st_ref_get(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_14 = l_Lean_instInhabitedParserDescr___closed__1;
x_15 = l_Array_empty___closed__1;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_st_mk_ref(x_16, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_18);
x_21 = l_Lean_PrettyPrinter_Formatter_fold(x_20, x_1, x_12, x_18, x_3, x_4, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Format_instInhabitedFormat;
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get(x_27, x_26, x_28);
lean_dec(x_26);
x_30 = 1;
x_31 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Format_instInhabitedFormat;
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get(x_35, x_34, x_36);
lean_dec(x_34);
x_38 = 1;
x_39 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_18);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_21, 0);
lean_dec(x_43);
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_21, 1);
x_48 = lean_ctor_get(x_21, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_51 = lean_nat_dec_eq(x_50, x_49);
lean_dec(x_49);
if (x_51 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_21);
lean_dec(x_41);
x_52 = l_Lean_PrettyPrinter_format___closed__3;
x_53 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_52, lean_box(0), x_3, x_4, x_47);
lean_dec(x_4);
lean_dec(x_3);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_57 = lean_nat_dec_eq(x_56, x_55);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
x_59 = l_Lean_PrettyPrinter_format___closed__3;
x_60 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_59, lean_box(0), x_3, x_4, x_54);
lean_dec(x_4);
lean_dec(x_3);
return x_60;
}
}
}
}
}
block_72:
{
if (x_62 == 0)
{
x_6 = x_63;
goto block_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_2);
x_64 = l_Lean_fmt___at_Lean_PrettyPrinter_Formatter_categoryParser_formatter___spec__2(x_2);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_PrettyPrinter_format___closed__5;
x_70 = l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__1(x_69, x_68, x_3, x_4, x_63);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_6 = x_71;
goto block_61;
}
}
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_format___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_format___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___kind_term____x40_Init_Notation___hyg_3____closed__16;
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
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3894____closed__4;
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
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_3026_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5;
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
l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1 = _init_l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1);
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
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__5);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__6);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__7);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM);
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
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__5);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__6);
l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__7);
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
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__1);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__4);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__5);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__6);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__7);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__8 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__8);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__9 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__9);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__10 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__10);
l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__11 = _init_l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbol_formatter___closed__11);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbol_formatter___closed__3);
l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1 = _init_l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1();
lean_mark_persistent(l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__1);
l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2 = _init_l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2();
lean_mark_persistent(l_List_map___at_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___spec__2___closed__2);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1 = _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1);
res = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2393_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Formatter_formatterAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterAliasesRef);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__1 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__1);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__2 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__2);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__3 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__3);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__4 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__4);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__5 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__5);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__6 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__6);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__7 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__7);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__8 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__8);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__9 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__9);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__10 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__10);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__11 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__11);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__12 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__12);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__13 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__13);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__14 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__14);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__15 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__15);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__16 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__16);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__17 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__17);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__18 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__18);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__19 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__19);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__20 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__20);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__21 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__21);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__22 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__22);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__23 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__23();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__23);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__24 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__24();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__24);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__25 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__25();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__25);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__26 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__26();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__26);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__27 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__27();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__27);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__28 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__28();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__28);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__29 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__29();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__29);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__30 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__30();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__30);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__31 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__31();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__31);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__32 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__32();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__32);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__33 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__33();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__33);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__34 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__34();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__34);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__35 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__35();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__35);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__36 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__36();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__36);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__37 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__37();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__37);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__38 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__38();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__38);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__39 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__39();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__39);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__40 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__40();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__40);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__41 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__41();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__41);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__42 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__42();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__42);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__43 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__43();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__43);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__44 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__44();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__44);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__45 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__45();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__45);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__46 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__46();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__46);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__47 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__47();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__47);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__48 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__48();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__48);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__49 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__49();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__49);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__50 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__50();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__50);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__51 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__51();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__51);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__52 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__52();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__52);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__53 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__53();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__53);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__54 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__54();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__54);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__55 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__55();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__55);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__56 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__56();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__56);
l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__57 = _init_l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__57();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460____closed__57);
res = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_2460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_format___closed__1 = _init_l_Lean_PrettyPrinter_format___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__1);
l_Lean_PrettyPrinter_format___closed__2 = _init_l_Lean_PrettyPrinter_format___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__2);
l_Lean_PrettyPrinter_format___closed__3 = _init_l_Lean_PrettyPrinter_format___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__3);
l_Lean_PrettyPrinter_format___closed__4 = _init_l_Lean_PrettyPrinter_format___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__4);
l_Lean_PrettyPrinter_format___closed__5 = _init_l_Lean_PrettyPrinter_format___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__5);
l_Lean_PrettyPrinter_formatTerm___closed__1 = _init_l_Lean_PrettyPrinter_formatTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTerm___closed__1);
l_Lean_PrettyPrinter_formatCommand___closed__1 = _init_l_Lean_PrettyPrinter_formatCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__1);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_3026_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
