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
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_pushNone;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_epsilon___closed__0;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Toml_strAtom_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_lit___closed__2;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object*);
static double l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object*, uint32_t, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__0;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object*, uint8_t);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Toml_strAtom_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__4;
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Toml_strAtom_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_lit___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__1;
LEAN_EXPORT uint8_t l_Lake_Toml_isHexDigit(uint32_t);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__2;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_sepByChar1Fn___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isBinDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2;
static lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0;
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_Toml_lit___closed__0;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Toml_strAtom_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__5;
static lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__2;
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
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
static lean_object* _init_l_Lake_Toml_instAndThenParserFn__lake() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0), 4, 0);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_3);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_5, x_9);
lean_dec(x_5);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Parser_ParserState_stackSize(x_3);
lean_dec_ref(x_3);
x_12 = l_Lean_Parser_ParserState_restore(x_4, x_11, x_9);
lean_dec(x_11);
return x_12;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
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
x_8 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_6, x_7);
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
x_7 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_5, x_6);
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
x_11 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_9, x_10);
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
lean_inc_ref(x_3);
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_Parser_ParserContext_mkEmptySubstringAt(x_3, x_1);
lean_dec_ref(x_3);
x_13 = lean_string_utf8_extract(x_7, x_1, x_6);
x_21 = lean_nat_dec_le(x_11, x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_11);
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
lean_ctor_set(x_23, 2, x_11);
x_14 = x_23;
goto block_20;
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_string_utf8_byte_size(x_13);
x_16 = lean_nat_add(x_1, x_15);
lean_dec(x_15);
if (lean_is_scalar(x_9)) {
 x_17 = lean_alloc_ctor(0, 4, 0);
} else {
 x_17 = x_9;
}
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = l_Lean_Parser_ParserState_pushSyntax(x_10, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = l_Lake_Toml_pushAtom(x_9, x_2, x_3, x_5);
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
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_atom___lam__0___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_atom___lam__1___boxed), 1, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_atomFn), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
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
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_atom___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_Syntax_Traverser_left(x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_st_ref_set(x_1, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_22 = l_Lean_Syntax_Traverser_left(x_16);
x_23 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 2, x_20);
x_24 = lean_st_ref_set(x_1, x_23, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg(x_1, x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_2, 2);
x_11 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2;
x_12 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6;
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_2, 2);
x_19 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2;
x_20 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6;
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_18);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
}
static double _init_l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3(x_2, x_3, x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_st_ref_take(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 4);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; double x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_22 = 0;
x_23 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_22);
x_25 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_9);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_6);
lean_ctor_set(x_11, 1, x_26);
lean_ctor_set(x_11, 0, x_6);
x_27 = l_Lean_PersistentArray_push___redArg(x_20, x_11);
lean_ctor_set(x_13, 0, x_27);
x_28 = lean_st_ref_set(x_4, x_12, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_30);
return x_7;
}
else
{
uint64_t x_31; lean_object* x_32; double x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_34 = 0;
x_35 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_36 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_float(x_36, sizeof(void*)*2, x_33);
lean_ctor_set_float(x_36, sizeof(void*)*2 + 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*2 + 16, x_34);
x_37 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_38 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_6);
lean_ctor_set(x_11, 1, x_38);
lean_ctor_set(x_11, 0, x_6);
x_39 = l_Lean_PersistentArray_push___redArg(x_32, x_11);
x_40 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint64(x_40, sizeof(void*)*1, x_31);
lean_ctor_set(x_12, 4, x_40);
x_41 = lean_st_ref_set(x_4, x_12, x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_box(0);
lean_ctor_set(x_7, 1, x_42);
lean_ctor_set(x_7, 0, x_43);
return x_7;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; double x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
x_46 = lean_ctor_get(x_12, 2);
x_47 = lean_ctor_get(x_12, 3);
x_48 = lean_ctor_get(x_12, 5);
x_49 = lean_ctor_get(x_12, 6);
x_50 = lean_ctor_get(x_12, 7);
x_51 = lean_ctor_get(x_12, 8);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_52 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_53 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_54 = x_13;
} else {
 lean_dec_ref(x_13);
 x_54 = lean_box(0);
}
x_55 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_56 = 0;
x_57 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_58 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_float(x_58, sizeof(void*)*2, x_55);
lean_ctor_set_float(x_58, sizeof(void*)*2 + 8, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 16, x_56);
x_59 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_6);
lean_ctor_set(x_11, 1, x_60);
lean_ctor_set(x_11, 0, x_6);
x_61 = l_Lean_PersistentArray_push___redArg(x_53, x_11);
if (lean_is_scalar(x_54)) {
 x_62 = lean_alloc_ctor(0, 1, 8);
} else {
 x_62 = x_54;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint64(x_62, sizeof(void*)*1, x_52);
x_63 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_45);
lean_ctor_set(x_63, 2, x_46);
lean_ctor_set(x_63, 3, x_47);
lean_ctor_set(x_63, 4, x_62);
lean_ctor_set(x_63, 5, x_48);
lean_ctor_set(x_63, 6, x_49);
lean_ctor_set(x_63, 7, x_50);
lean_ctor_set(x_63, 8, x_51);
x_64 = lean_st_ref_set(x_4, x_63, x_15);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_box(0);
lean_ctor_set(x_7, 1, x_65);
lean_ctor_set(x_7, 0, x_66);
return x_7;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; lean_object* x_79; double x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_dec(x_11);
x_68 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_12, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_12, 5);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_12, 6);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_12, 7);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_12, 8);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 x_76 = x_12;
} else {
 lean_dec_ref(x_12);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_78 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_78);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_79 = x_13;
} else {
 lean_dec_ref(x_13);
 x_79 = lean_box(0);
}
x_80 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_81 = 0;
x_82 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_83 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set_float(x_83, sizeof(void*)*2, x_80);
lean_ctor_set_float(x_83, sizeof(void*)*2 + 8, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*2 + 16, x_81);
x_84 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_85 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_9);
lean_ctor_set(x_85, 2, x_84);
lean_inc(x_6);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_6);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_PersistentArray_push___redArg(x_78, x_86);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 1, 8);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set_uint64(x_88, sizeof(void*)*1, x_77);
if (lean_is_scalar(x_76)) {
 x_89 = lean_alloc_ctor(0, 9, 0);
} else {
 x_89 = x_76;
}
lean_ctor_set(x_89, 0, x_68);
lean_ctor_set(x_89, 1, x_69);
lean_ctor_set(x_89, 2, x_70);
lean_ctor_set(x_89, 3, x_71);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_72);
lean_ctor_set(x_89, 6, x_73);
lean_ctor_set(x_89, 7, x_74);
lean_ctor_set(x_89, 8, x_75);
x_90 = lean_st_ref_set(x_4, x_89, x_67);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_box(0);
lean_ctor_set(x_7, 1, x_91);
lean_ctor_set(x_7, 0, x_92);
return x_7;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; double x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_93 = lean_ctor_get(x_7, 0);
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_7);
x_95 = lean_st_ref_take(x_4, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 4);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 2);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_96, 3);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_96, 5);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_96, 6);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_96, 7);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_96, 8);
lean_inc_ref(x_107);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 lean_ctor_release(x_96, 5);
 lean_ctor_release(x_96, 6);
 lean_ctor_release(x_96, 7);
 lean_ctor_release(x_96, 8);
 x_108 = x_96;
} else {
 lean_dec_ref(x_96);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get_uint64(x_97, sizeof(void*)*1);
x_110 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
x_112 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
x_113 = 0;
x_114 = l_Lake_Toml_mkUnexpectedCharError___closed__1;
x_115 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_float(x_115, sizeof(void*)*2, x_112);
lean_ctor_set_float(x_115, sizeof(void*)*2 + 8, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*2 + 16, x_113);
x_116 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1;
x_117 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_93);
lean_ctor_set(x_117, 2, x_116);
lean_inc(x_6);
if (lean_is_scalar(x_99)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_99;
}
lean_ctor_set(x_118, 0, x_6);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_PersistentArray_push___redArg(x_110, x_118);
if (lean_is_scalar(x_111)) {
 x_120 = lean_alloc_ctor(0, 1, 8);
} else {
 x_120 = x_111;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set_uint64(x_120, sizeof(void*)*1, x_109);
if (lean_is_scalar(x_108)) {
 x_121 = lean_alloc_ctor(0, 9, 0);
} else {
 x_121 = x_108;
}
lean_ctor_set(x_121, 0, x_100);
lean_ctor_set(x_121, 1, x_101);
lean_ctor_set(x_121, 2, x_102);
lean_ctor_set(x_121, 3, x_103);
lean_ctor_set(x_121, 4, x_120);
lean_ctor_set(x_121, 5, x_104);
lean_ctor_set(x_121, 6, x_105);
lean_ctor_set(x_121, 7, x_106);
lean_ctor_set(x_121, 8, x_107);
x_122 = lean_st_ref_set(x_4, x_121, x_98);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
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
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_10);
x_11 = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_7);
lean_dec_ref(x_7);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_13);
lean_inc(x_2);
x_15 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_11, x_14, x_1, x_2, x_3, x_4, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg(x_2, x_16);
lean_dec(x_2);
return x_17;
}
else
{
lean_dec(x_2);
return x_15;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = l_Lake_Toml_atom_formatter___redArg___closed__3;
x_22 = l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg(x_21, x_3, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_6);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_22, 1);
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = l_Lake_Toml_atom_formatter___redArg___closed__5;
x_31 = lean_box(0);
x_32 = 0;
x_33 = l_Lean_Syntax_formatStx(x_7, x_31, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_34);
lean_ctor_set(x_22, 0, x_30);
x_35 = l_Lake_Toml_atom_formatter___redArg___closed__7;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_22);
x_36 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(x_21, x_6, x_3, x_4, x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_dec(x_22);
x_40 = l_Lake_Toml_atom_formatter___redArg___closed__5;
x_41 = lean_box(0);
x_42 = 0;
x_43 = l_Lean_Syntax_formatStx(x_7, x_41, x_42);
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_Toml_atom_formatter___redArg___closed__7;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_46);
lean_ctor_set(x_6, 0, x_45);
x_47 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(x_21, x_6, x_3, x_4, x_39);
lean_dec(x_4);
lean_dec_ref(x_3);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_dec(x_6);
x_51 = l_Lake_Toml_atom_formatter___redArg___closed__3;
x_52 = l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg(x_51, x_3, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec_ref(x_52);
x_56 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
x_59 = l_Lake_Toml_atom_formatter___redArg___closed__5;
x_60 = lean_box(0);
x_61 = 0;
x_62 = l_Lean_Syntax_formatStx(x_7, x_60, x_61);
x_63 = l_Lean_MessageData_ofFormat(x_62);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_58;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lake_Toml_atom_formatter___redArg___closed__7;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(x_51, x_66, x_3, x_4, x_57);
lean_dec(x_4);
lean_dec_ref(x_3);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_68);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_atom_formatter___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lake_Toml_atom_formatter_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lake_Toml_atom_formatter_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_atom_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_chAtom_formatter___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l_Lake_Toml_chAtom_formatter___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_10 = l_Lake_Toml_chAtom_formatter(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_chAtom_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; lean_object* x_10; 
x_9 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_10 = l_Lake_Toml_chAtom_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Toml_strAtom_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Toml_strAtom_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
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
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = l_Substring_takeWhileAux___at___Lake_Toml_strAtom_spec__0(x_1, x_5, x_4);
x_7 = l_Substring_takeRightWhileAux___at___Lake_Toml_strAtom_spec__1(x_1, x_6, x_5);
x_8 = lean_string_utf8_extract(x_1, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lake_Toml_atom(x_9, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Toml_strAtom_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_Toml_strAtom_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Toml_strAtom_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_Toml_strAtom_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_strAtom(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_strAtom_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_strAtom_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_strAtom_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_inc_ref(x_4);
x_11 = lean_apply_2(x_3, x_4, x_5);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_inc(x_2);
x_13 = l_Lean_Parser_ParserContext_mkEmptySubstringAt(x_4, x_2);
lean_dec_ref(x_4);
x_14 = lean_string_utf8_extract(x_8, x_2, x_7);
x_20 = lean_nat_dec_le(x_12, x_9);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_12);
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
lean_ctor_set(x_22, 2, x_12);
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
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_7);
x_17 = l_Lean_Syntax_mkLit(x_1, x_14, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_6 = lean_apply_2(x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_Option_instBEq_beq___at___Lake_Toml_optFn_spec__0(x_7, x_8);
if (x_9 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = l_Lake_Toml_pushLit(x_1, x_10, x_3, x_4, x_6);
return x_11;
}
}
}
static lean_object* _init_l_Lake_Toml_lit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_atom___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_lit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_atom___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_lit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lake_Toml_lit___closed__1;
x_3 = l_Lake_Toml_lit___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_Toml_lit___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_lit_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_lit_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Toml_lit_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0), 6, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(x_3);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_9, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lake_Toml_litWithAntiquot_formatter(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_10 = 0;
x_11 = lean_box(x_3);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_9, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lake_Toml_litWithAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_Toml_epsilon___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_epsilonInfo;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Toml_epsilon___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_formatter___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
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
case 0:
{
lean_dec_ref(x_1);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_nat_dec_lt(x_8, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_10; 
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_array_fget(x_5, x_8);
x_15 = lean_box(0);
x_16 = lean_array_fset(x_5, x_8, x_15);
x_17 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(x_1, x_14);
x_18 = lean_array_fset(x_16, x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_19 = lean_array_fget(x_5, x_8);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_5, x_8, x_20);
x_22 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(x_1, x_19);
x_23 = lean_array_fset(x_21, x_8, x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
}
case 2:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_apply_1(x_1, x_26);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_30 = lean_apply_1(x_1, x_28);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_apply_1(x_1, x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_2);
x_39 = lean_apply_1(x_1, x_35);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_1);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_nat_dec_lt(x_8, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_10; 
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_array_fget(x_5, x_8);
x_15 = lean_box(0);
x_16 = lean_array_fset(x_5, x_8, x_15);
x_17 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0(x_1, x_14);
x_18 = lean_array_fset(x_16, x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_19 = lean_array_fget(x_5, x_8);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_5, x_8, x_20);
x_22 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0(x_1, x_19);
x_23 = lean_array_fset(x_21, x_8, x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
}
case 2:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_26);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_30 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_28);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_2);
x_39 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0___lam__0(x_1, x_35);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
return x_40;
}
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
x_9 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___Lake_Toml_extendTrailingFn_spec__0(x_6, x_7);
x_10 = l_Lean_Parser_ParserState_pushSyntax(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_formatter___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_formatter___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_trailing_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_trailing_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_3 = l_Lake_Toml_epsilon___closed__0;
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
x_2 = l_Lake_Toml_lit___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_atom_formatter_spec__0___redArg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_Syntax_getKind(x_7);
x_10 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_9, x_1, x_2, x_3, x_4, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_Syntax_getKind(x_7);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(x_9, x_1, x_2, x_3, x_4, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lake_Toml_dynamicNode_parenthesizer_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_dynamicNode_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_recNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_dynamicNode_parenthesizer___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_recNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_16, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lake_Toml_recNodeWithAntiquot_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_16, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = 1;
lean_inc(x_2);
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
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sepBy", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0___boxed), 5, 0);
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_9 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_7);
x_13 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_10, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepByLinebreak_formatter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_9 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_7);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_10, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepByLinebreak_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
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
lean_object* x_1; 
x_1 = l_Lean_Parser_pushNone;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_sepByLinebreak___closed__3;
x_2 = l_Lake_Toml_sepByLinebreak___closed__2;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_4 = l_Lake_Toml_sepByLinebreak___closed__0;
x_5 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_4);
x_6 = l_Lake_Toml_sepByLinebreak___closed__4;
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
static lean_object* _init_l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_8 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__1;
x_11 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepBy1Linebreak_formatter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_8 = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__1;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lake_Toml_sepBy1Linebreak_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1;
x_4 = l_Lake_Toml_sepByLinebreak___closed__0;
x_5 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_4);
x_6 = l_Lake_Toml_sepByLinebreak___closed__4;
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
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_ParserUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0 = _init_l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0();
lean_mark_persistent(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0);
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
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__0 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__0);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__1);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__2);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__3);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__4 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__4);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__5 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__5);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3_spec__3___closed__6);
l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0 = _init_l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__0();
l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1 = _init_l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lake_Toml_atom_formatter_spec__3___redArg___closed__1);
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
l_Lake_Toml_lit___closed__0 = _init_l_Lake_Toml_lit___closed__0();
lean_mark_persistent(l_Lake_Toml_lit___closed__0);
l_Lake_Toml_lit___closed__1 = _init_l_Lake_Toml_lit___closed__1();
lean_mark_persistent(l_Lake_Toml_lit___closed__1);
l_Lake_Toml_lit___closed__2 = _init_l_Lake_Toml_lit___closed__2();
lean_mark_persistent(l_Lake_Toml_lit___closed__2);
l_Lake_Toml_epsilon___closed__0 = _init_l_Lake_Toml_epsilon___closed__0();
lean_mark_persistent(l_Lake_Toml_epsilon___closed__0);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2);
l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3 = _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3);
l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0 = _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0);
l_Lake_Toml_sepByLinebreak___closed__0 = _init_l_Lake_Toml_sepByLinebreak___closed__0();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__0);
l_Lake_Toml_sepByLinebreak___closed__1 = _init_l_Lake_Toml_sepByLinebreak___closed__1();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__1);
l_Lake_Toml_sepByLinebreak___closed__2 = _init_l_Lake_Toml_sepByLinebreak___closed__2();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__2);
l_Lake_Toml_sepByLinebreak___closed__3 = _init_l_Lake_Toml_sepByLinebreak___closed__3();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__3);
l_Lake_Toml_sepByLinebreak___closed__4 = _init_l_Lake_Toml_sepByLinebreak___closed__4();
lean_mark_persistent(l_Lake_Toml_sepByLinebreak___closed__4);
l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__0 = _init_l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__0);
l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__1 = _init_l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_sepBy1Linebreak_formatter___redArg___closed__1);
l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__0 = _init_l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__0();
lean_mark_persistent(l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__0);
l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__1 = _init_l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__1();
lean_mark_persistent(l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
