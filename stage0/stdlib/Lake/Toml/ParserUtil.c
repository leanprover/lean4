// Lean compiler output
// Module: Lake.Toml.ParserUtil
// Imports: public import Lean.PrettyPrinter.Formatter public import Lean.PrettyPrinter.Parenthesizer import Lean.Parser
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_pushNone;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object*);
static lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object*);
static lean_object* l_Lake_Toml_atom___closed__2;
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object*);
static double l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object*, uint32_t, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0;
static lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object*, uint8_t);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4;
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg();
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake;
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__6;
lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
static lean_object* l_Lake_Toml_sepByLinebreak___closed__1;
LEAN_EXPORT uint8_t l_Lake_Toml_isHexDigit(uint32_t);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__2;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
static lean_object* l_Lake_Toml_sepByChar1Fn___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_instAndThenParserFn__lake___closed__0;
LEAN_EXPORT uint8_t l_Lake_Toml_isBinDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2;
static lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0;
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom___closed__0;
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isOctDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__3;
lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5;
static lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__2;
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isBinDigit(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 49;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_isBinDigit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isOctDigit(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 55;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_isOctDigit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isHexDigit(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint32_t x_14; uint8_t x_15; 
x_14 = 48;
x_15 = lean_uint32_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_8 = x_15;
goto block_13;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 57;
x_17 = lean_uint32_dec_le(x_1, x_16);
x_8 = x_17;
goto block_13;
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 65;
x_4 = lean_uint32_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 70;
x_6 = lean_uint32_dec_le(x_1, x_5);
return x_6;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 97;
x_10 = lean_uint32_dec_le(x_9, x_1);
if (x_10 == 0)
{
x_2 = x_10;
goto block_7;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 102;
x_12 = lean_uint32_dec_le(x_1, x_11);
x_2 = x_12;
goto block_7;
}
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_isHexDigit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_skipFn___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_skipFn(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instBEqError_beq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc_ref(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0;
x_8 = lean_box(0);
x_9 = l_Option_instBEq_beq___redArg(x_7, x_6, x_8);
if (x_9 == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_apply_3(x_2, x_10, x_3, x_5);
return x_11;
}
}
}
static lean_object* _init_l_Lake_Toml_instAndThenParserFn__lake___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_instAndThenParserFn__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_instAndThenParserFn__lake___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_apply_3(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_dec_ref(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_Parser_instBEqError_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l_Lean_Parser_ParserState_stackSize(x_3);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_7, x_4);
lean_dec(x_7);
if (x_11 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_restore(x_6, x_5, x_4);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_7 = lean_apply_2(x_1, x_2, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0;
x_10 = lean_box(0);
x_11 = l_Option_instBEq_beq___redArg(x_9, x_8, x_10);
if (x_11 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(x_2, x_3, x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_mkUnexpectedCharError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_mkUnexpectedCharError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_mkUnexpectedCharError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object* x_1, uint32_t x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lake_Toml_mkUnexpectedCharError___closed__0;
x_6 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_7 = lean_string_push(x_6, x_2);
x_8 = lean_string_append(x_5, x_7);
lean_dec_ref(x_7);
x_9 = l_Lake_Toml_mkUnexpectedCharError___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_10, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_4);
x_7 = l_Lake_Toml_mkUnexpectedCharError(x_1, x_5, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 2);
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Parser_InputContext_atEnd(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_string_utf8_get_fast(x_8, x_5);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = l_Lake_Toml_mkUnexpectedCharError(x_4, x_9, x_2, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_5);
lean_dec(x_2);
x_15 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_5);
lean_dec(x_5);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = l_Lean_Parser_ParserState_mkEOIError(x_4, x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Toml_satisfyFn(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_3, 0);
x_13 = l_Lean_Parser_InputContext_atEnd(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_string_utf8_get_fast(x_14, x_11);
x_16 = lean_box_uint32(x_15);
lean_inc_ref(x_1);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
x_19 = 1;
x_20 = l_Lake_Toml_mkUnexpectedCharError(x_4, x_15, x_2, x_19);
x_5 = x_20;
goto block_10;
}
else
{
lean_object* x_21; 
lean_inc(x_11);
lean_dec(x_2);
x_21 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_11);
lean_dec(x_11);
x_5 = x_21;
goto block_10;
}
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Parser_ParserState_mkEOIError(x_4, x_2);
x_5 = x_22;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 4);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Parser_takeWhileFn(x_1, x_3, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Toml_takeWhile1Fn(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_Parser_InputContext_atEnd(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; uint32_t x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_string_utf8_get_fast(x_7, x_4);
x_14 = 48;
x_15 = lean_uint32_dec_le(x_14, x_8);
if (x_15 == 0)
{
x_9 = x_15;
goto block_13;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 57;
x_17 = lean_uint32_dec_le(x_8, x_16);
x_9 = x_17;
goto block_13;
}
block_13:
{
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lake_Toml_mkUnexpectedCharError(x_3, x_8, x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc(x_4);
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_4);
lean_dec(x_4);
return x_12;
}
}
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_digitFn(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lake_Toml_digitFn(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_8; 
x_8 = l_Lake_Toml_digitFn(x_1, x_2, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_digitPairFn(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 2);
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Parser_InputContext_atEnd(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_string_utf8_get_fast(x_8, x_5);
x_10 = lean_uint32_dec_eq(x_9, x_1);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lake_Toml_mkUnexpectedCharError(x_4, x_9, x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_5);
lean_dec(x_2);
x_13 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_5);
lean_dec(x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_mkEOIError(x_4, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lake_Toml_chFn(x_5, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_string_utf8_get_fast(x_1, x_3);
lean_inc(x_2);
x_8 = l_Lake_Toml_chFn(x_7, x_2, x_4, x_5);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
if (x_6 == 0)
{
lean_object* x_12; 
x_12 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_3 = x_12;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
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
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_strAuxFn(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_strAuxFn___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = l_Lean_Parser_atomicFn(x_6, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_Toml_sepByChar1Fn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected separator '", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 2);
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_Parser_InputContext_atEnd(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_6);
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_string_utf8_get_fast(x_9, x_6);
x_11 = l_Lean_Parser_ParserState_next_x27___redArg(x_5, x_4, x_6);
lean_dec(x_6);
x_12 = lean_box_uint32(x_10);
lean_inc_ref(x_1);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
lean_dec_ref(x_1);
x_15 = 1;
x_16 = lean_uint32_dec_eq(x_10, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lake_Toml_mkUnexpectedCharError(x_11, x_10, x_3, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_Lake_Toml_sepByChar1Fn___closed__0;
x_19 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_20 = lean_string_push(x_19, x_10);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = l_Lake_Toml_mkUnexpectedCharError___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_Parser_ParserState_mkUnexpectedError(x_11, x_23, x_3, x_15);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = l_Lake_Toml_sepByChar1AuxFn(x_1, x_2, x_3, x_4, x_11);
return x_25;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 2);
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_Parser_InputContext_atEnd(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_string_utf8_get_fast(x_9, x_6);
x_11 = lean_box_uint32(x_10);
lean_inc_ref(x_1);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_uint32_dec_eq(x_10, x_2);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_6);
x_15 = l_Lean_Parser_ParserState_next_x27___redArg(x_5, x_4, x_6);
lean_dec(x_6);
x_16 = l_Lake_Toml_sepByChar1Fn(x_1, x_2, x_3, x_4, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_inc(x_6);
x_17 = l_Lean_Parser_ParserState_next_x27___redArg(x_5, x_4, x_6);
lean_dec(x_6);
x_5 = x_17;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l_Lake_Toml_sepByChar1AuxFn(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l_Lake_Toml_sepByChar1Fn(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_21; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
lean_inc(x_1);
x_10 = l_Lean_Parser_ParserContext_mkEmptySubstringAt(x_3, x_1);
x_11 = lean_apply_2(x_2, x_3, x_4);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_string_utf8_extract(x_7, x_1, x_6);
x_21 = lean_nat_dec_le(x_12, x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_8);
x_14 = x_22;
goto block_20;
}
else
{
lean_object* x_23; 
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_12);
x_14 = x_23;
goto block_20;
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_string_utf8_byte_size(x_13);
x_16 = lean_nat_add(x_1, x_15);
if (lean_is_scalar(x_9)) {
 x_17 = lean_alloc_ctor(0, 4, 0);
} else {
 x_17 = x_9;
}
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_inc_ref(x_3);
x_6 = lean_apply_2(x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_Toml_pushAtom(x_5, x_2, x_3, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_atom___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_atom___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_atom___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_atom___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_atom___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lake_Toml_atom___closed__1;
x_3 = l_Lake_Toml_atom___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_Toml_atom___closed__2;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_atomFn), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Syntax_Traverser_left(x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_16 = l_Lean_Syntax_Traverser_left(x_10);
x_17 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_14);
x_18 = lean_st_ref_set(x_1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__6;
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(x_2, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_st_ref_take(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; double x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_16 = 0;
x_17 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_15);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_16);
x_19 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_19);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_PersistentArray_push___redArg(x_14, x_21);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_st_ref_set(x_4, x_10);
x_24 = lean_box(0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
uint64_t x_25; lean_object* x_26; double x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_28 = 0;
x_29 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_28);
x_31 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_PersistentArray_push___redArg(x_26, x_33);
x_35 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint64(x_35, sizeof(void*)*1, x_25);
lean_ctor_set(x_10, 4, x_35);
x_36 = lean_st_ref_set(x_4, x_10);
x_37 = lean_box(0);
lean_ctor_set(x_7, 0, x_37);
return x_7;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; double x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_38 = lean_ctor_get(x_10, 4);
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
x_41 = lean_ctor_get(x_10, 2);
x_42 = lean_ctor_get(x_10, 3);
x_43 = lean_ctor_get(x_10, 5);
x_44 = lean_ctor_get(x_10, 6);
x_45 = lean_ctor_get(x_10, 7);
x_46 = lean_ctor_get(x_10, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_47 = lean_ctor_get_uint64(x_38, sizeof(void*)*1);
x_48 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
x_50 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_51 = 0;
x_52 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_53 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_float(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_float(x_53, sizeof(void*)*2 + 8, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 16, x_51);
x_54 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_55 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_9);
lean_ctor_set(x_55, 2, x_54);
lean_inc(x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_PersistentArray_push___redArg(x_48, x_56);
if (lean_is_scalar(x_49)) {
 x_58 = lean_alloc_ctor(0, 1, 8);
} else {
 x_58 = x_49;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint64(x_58, sizeof(void*)*1, x_47);
x_59 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_41);
lean_ctor_set(x_59, 3, x_42);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_43);
lean_ctor_set(x_59, 6, x_44);
lean_ctor_set(x_59, 7, x_45);
lean_ctor_set(x_59, 8, x_46);
x_60 = lean_st_ref_set(x_4, x_59);
x_61 = lean_box(0);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; double x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_st_ref_take(x_4);
x_64 = lean_ctor_get(x_63, 4);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_63, 5);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_63, 6);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_63, 7);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_63, 8);
lean_inc_ref(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 lean_ctor_release(x_63, 7);
 lean_ctor_release(x_63, 8);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get_uint64(x_64, sizeof(void*)*1);
x_75 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
x_77 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_78 = 0;
x_79 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_80 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_float(x_80, sizeof(void*)*2, x_77);
lean_ctor_set_float(x_80, sizeof(void*)*2 + 8, x_77);
lean_ctor_set_uint8(x_80, sizeof(void*)*2 + 16, x_78);
x_81 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_82 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_62);
lean_ctor_set(x_82, 2, x_81);
lean_inc(x_6);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_PersistentArray_push___redArg(x_75, x_83);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 1, 8);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint64(x_85, sizeof(void*)*1, x_74);
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(0, 9, 0);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_66);
lean_ctor_set(x_86, 2, x_67);
lean_ctor_set(x_86, 3, x_68);
lean_ctor_set(x_86, 4, x_85);
lean_ctor_set(x_86, 5, x_69);
lean_ctor_set(x_86, 6, x_70);
lean_ctor_set(x_86, 7, x_71);
lean_ctor_set(x_86, 8, x_72);
x_87 = lean_st_ref_set(x_4, x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("format", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_atom_formatter___redArg___closed__2;
x_2 = l_Lake_Toml_atom_formatter___redArg___closed__1;
x_3 = l_Lake_Toml_atom_formatter___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected syntax '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_atom_formatter___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', expected atom", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_atom_formatter___redArg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_9);
x_10 = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_7);
lean_dec_ref(x_7);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_12);
lean_inc(x_2);
x_14 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_10, x_13, x_1, x_2, x_3, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_14);
x_15 = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(x_2);
lean_dec(x_2);
return x_15;
}
else
{
lean_dec(x_2);
return x_14;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = l_Lake_Toml_atom_formatter___redArg___closed__3;
x_17 = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(x_16, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = l_Lake_Toml_atom_formatter___redArg___closed__5;
x_22 = lean_box(0);
x_23 = 0;
x_24 = l_Lean_Syntax_formatStx(x_7, x_22, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lake_Toml_atom_formatter___redArg___closed__7;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(x_16, x_28, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec_ref(x_29);
x_30 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return x_30;
}
else
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_atom_formatter___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_atom_formatter___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_atom_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box_uint32(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lake_Toml_atom(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lake_Toml_chAtom(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l_Lake_Toml_chAtom_formatter___redArg(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_chAtom_formatter___redArg(x_1, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_10 = l_Lake_Toml_chAtom_formatter(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_chAtom_parenthesizer___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_10 = l_Lake_Toml_chAtom_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_trimAscii(x_6);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_string_utf8_extract(x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lake_Toml_atom(x_12, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_strAtom_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_strAtom_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_strAtom_parenthesizer___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_strAtom_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_20; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
lean_inc(x_2);
x_11 = l_Lean_Parser_ParserContext_mkEmptySubstringAt(x_4, x_2);
x_12 = lean_apply_2(x_3, x_4, x_5);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_string_utf8_extract(x_8, x_2, x_7);
x_20 = lean_nat_dec_le(x_13, x_9);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set(x_21, 2, x_9);
x_15 = x_21;
goto block_19;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_inc(x_7);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_13);
x_15 = x_22;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(0, 4, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_7);
x_17 = l_Lean_Syntax_mkLit(x_1, x_14, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_12, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_inc_ref(x_4);
x_7 = lean_apply_2(x_2, x_4, x_5);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_11; 
x_11 = l_Lake_Toml_pushLit(x_1, x_6, x_3, x_4, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_Toml_atom___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_lit_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_lit_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_lit_parenthesizer___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_lit_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(x_3);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_9, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lake_Toml_litWithAntiquot_formatter(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0;
x_10 = 0;
x_11 = lean_box(x_3);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_9, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lake_Toml_litWithAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 0;
lean_inc(x_2);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
x_8 = l_Lake_Toml_lit(x_2, x_3, x_4);
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lake_Toml_litWithAntiquot(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_formatter___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_formatter___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_parenthesizer___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
case 3:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_17 = lean_apply_1(x_1, x_13);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
return x_18;
}
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
x_25 = lean_nat_dec_lt(x_24, x_22);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_26; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_2, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = lean_array_fget(x_21, x_24);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_21, x_24, x_31);
x_33 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(x_1, x_30);
x_34 = lean_array_fset(x_32, x_24, x_33);
lean_dec(x_24);
lean_ctor_set(x_2, 2, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_35 = lean_array_fget(x_21, x_24);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_21, x_24, x_36);
x_38 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(x_1, x_35);
x_39 = lean_array_fset(x_37, x_24, x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_39);
return x_40;
}
}
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 2);
lean_dec(x_6);
lean_ctor_set(x_4, 2, x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 x_16 = x_10;
} else {
 lean_dec_ref(x_10);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(0, 3, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_1);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_13);
return x_18;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_6);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
case 3:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_11);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_17 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_13);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
return x_18;
}
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
x_25 = lean_nat_dec_lt(x_24, x_22);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_26; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_2, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = lean_array_fget(x_21, x_24);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_21, x_24, x_31);
x_33 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(x_1, x_30);
x_34 = lean_array_fset(x_32, x_24, x_33);
lean_dec(x_24);
lean_ctor_set(x_2, 2, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_35 = lean_array_fget(x_21, x_24);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_21, x_24, x_36);
x_38 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(x_1, x_35);
x_39 = lean_array_fset(x_37, x_24, x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_39);
return x_40;
}
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_dec_ref(x_5);
x_8 = l_Lean_Parser_ParserState_popSyntax(x_4);
x_9 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(x_6, x_7);
x_10 = l_Lean_Parser_ParserState_pushSyntax(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_formatter___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_trailing_formatter___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_formatter___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_trailing_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg() {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_trailing_parenthesizer___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_parenthesizer___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_trailing_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Toml_atom___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_8, x_1, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_dynamicNode_formatter___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_formatter___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(x_8, x_1, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lake_Toml_dynamicNode(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_dynamicNode_formatter___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_recNode_formatter___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_formatter___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_recNode_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_recNode_parenthesizer___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_recNode_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lake_Toml_dynamicNode(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = 1;
lean_inc(x_2);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_4, x_6);
x_8 = lean_apply_1(x_3, x_5);
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
x_10 = l_Lean_Parser_withCache(x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = 1;
x_11 = lean_box(x_4);
x_12 = lean_box(x_10);
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_16, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lake_Toml_recNodeWithAntiquot_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = 1;
x_11 = lean_box(x_4);
x_12 = lean_box(x_10);
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_16, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = 1;
lean_inc(x_2);
lean_inc_ref(x_1);
x_6 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_4, x_5);
x_7 = lean_box(x_4);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_7);
x_9 = l_Lake_Toml_recNode(x_8);
x_10 = l_Lean_Parser_withAntiquot(x_6, x_9);
x_11 = l_Lean_Parser_withCache(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lake_Toml_recNodeWithAntiquot(x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sepBy", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5;
x_11 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_10, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepByLinebreak_formatter(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_8 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_10, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepByLinebreak_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("line break", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak___closed__1;
x_2 = l_Lean_Parser_checkLinebreakBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_pushNone;
x_2 = l_Lake_Toml_sepByLinebreak___closed__2;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_4 = l_Lake_Toml_sepByLinebreak___closed__0;
x_5 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_4);
x_6 = l_Lake_Toml_sepByLinebreak___closed__3;
x_7 = l_Lean_Parser_sepByNoAntiquot(x_5, x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_Toml_sepByLinebreak(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5;
x_11 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_10, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepBy1Linebreak_formatter(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_8 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_10, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepBy1Linebreak_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_4 = l_Lake_Toml_sepByLinebreak___closed__0;
x_5 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_4);
x_6 = l_Lake_Toml_sepByLinebreak___closed__3;
x_7 = l_Lean_Parser_sepBy1NoAntiquot(x_5, x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_Toml_sepBy1Linebreak(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_2(x_1, x_2, x_3);
return x_8;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_skipInsideQuot_formatter(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_skipInsideQuot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
lean_object* initialize_Lean_Parser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_ParserUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0 = _init_l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0();
lean_mark_persistent(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0);
l_Lake_Toml_instAndThenParserFn__lake___closed__0 = _init_l_Lake_Toml_instAndThenParserFn__lake___closed__0();
lean_mark_persistent(l_Lake_Toml_instAndThenParserFn__lake___closed__0);
l_Lake_Toml_instAndThenParserFn__lake = _init_l_Lake_Toml_instAndThenParserFn__lake();
lean_mark_persistent(l_Lake_Toml_instAndThenParserFn__lake);
l_Lake_Toml_mkUnexpectedCharError___closed__0 = _init_l_Lake_Toml_mkUnexpectedCharError___closed__0();
lean_mark_persistent(l_Lake_Toml_mkUnexpectedCharError___closed__0);
l_Lake_Toml_mkUnexpectedCharError___closed__1 = _init_l_Lake_Toml_mkUnexpectedCharError___closed__1();
lean_mark_persistent(l_Lake_Toml_mkUnexpectedCharError___closed__1);
l_Lake_Toml_mkUnexpectedCharError___closed__2 = _init_l_Lake_Toml_mkUnexpectedCharError___closed__2();
lean_mark_persistent(l_Lake_Toml_mkUnexpectedCharError___closed__2);
l_Lake_Toml_sepByChar1Fn___closed__0 = _init_l_Lake_Toml_sepByChar1Fn___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByChar1Fn___closed__0);
l_Lake_Toml_atom___closed__0 = _init_l_Lake_Toml_atom___closed__0();
lean_mark_persistent(l_Lake_Toml_atom___closed__0);
l_Lake_Toml_atom___closed__1 = _init_l_Lake_Toml_atom___closed__1();
lean_mark_persistent(l_Lake_Toml_atom___closed__1);
l_Lake_Toml_atom___closed__2 = _init_l_Lake_Toml_atom___closed__2();
lean_mark_persistent(l_Lake_Toml_atom___closed__2);
l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0 = _init_l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1 = _init_l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__6);
l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0();
l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1 = _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1);
l_Lake_Toml_atom_formatter___redArg___closed__0 = _init_l_Lake_Toml_atom_formatter___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__0);
l_Lake_Toml_atom_formatter___redArg___closed__1 = _init_l_Lake_Toml_atom_formatter___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__1);
l_Lake_Toml_atom_formatter___redArg___closed__2 = _init_l_Lake_Toml_atom_formatter___redArg___closed__2();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__2);
l_Lake_Toml_atom_formatter___redArg___closed__3 = _init_l_Lake_Toml_atom_formatter___redArg___closed__3();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__3);
l_Lake_Toml_atom_formatter___redArg___closed__4 = _init_l_Lake_Toml_atom_formatter___redArg___closed__4();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__4);
l_Lake_Toml_atom_formatter___redArg___closed__5 = _init_l_Lake_Toml_atom_formatter___redArg___closed__5();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__5);
l_Lake_Toml_atom_formatter___redArg___closed__6 = _init_l_Lake_Toml_atom_formatter___redArg___closed__6();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__6);
l_Lake_Toml_atom_formatter___redArg___closed__7 = _init_l_Lake_Toml_atom_formatter___redArg___closed__7();
lean_mark_persistent(l_Lake_Toml_atom_formatter___redArg___closed__7);
l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0 = _init_l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0 = _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0);
l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1 = _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1);
l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2 = _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
l_Lake_Toml_sepByLinebreak___closed__0 = _init_l_Lake_Toml_sepByLinebreak___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__0);
l_Lake_Toml_sepByLinebreak___closed__1 = _init_l_Lake_Toml_sepByLinebreak___closed__1();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__1);
l_Lake_Toml_sepByLinebreak___closed__2 = _init_l_Lake_Toml_sepByLinebreak___closed__2();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__2);
l_Lake_Toml_sepByLinebreak___closed__3 = _init_l_Lake_Toml_sepByLinebreak___closed__3();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
