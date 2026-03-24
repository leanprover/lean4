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
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT uint8_t l_Lake_Toml_isBinDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isOctDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isHexDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqError_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0 = (const lean_object*)&l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instAndThenParserFn__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instAndThenParserFn__lake___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instAndThenParserFn__lake___closed__0 = (const lean_object*)&l_Lake_Toml_instAndThenParserFn__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instAndThenParserFn__lake = (const lean_object*)&l_Lake_Toml_instAndThenParserFn__lake___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_mkUnexpectedCharError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__0 = (const lean_object*)&l_Lake_Toml_mkUnexpectedCharError___closed__0_value;
static const lean_string_object l_Lake_Toml_mkUnexpectedCharError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__1 = (const lean_object*)&l_Lake_Toml_mkUnexpectedCharError___closed__1_value;
static const lean_string_object l_Lake_Toml_mkUnexpectedCharError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_Toml_mkUnexpectedCharError___closed__2 = (const lean_object*)&l_Lake_Toml_mkUnexpectedCharError___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object*, uint32_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_sepByChar1Fn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unexpected separator '"};
static const lean_object* l_Lake_Toml_sepByChar1Fn___closed__0 = (const lean_object*)&l_Lake_Toml_sepByChar1Fn___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lake_Toml_atom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_atom___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_atom___closed__0 = (const lean_object*)&l_Lake_Toml_atom___closed__0_value;
static const lean_closure_object l_Lake_Toml_atom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_atom___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_atom___closed__1 = (const lean_object*)&l_Lake_Toml_atom___closed__1_value;
static const lean_ctor_object l_Lake_Toml_atom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_atom___closed__0_value),((lean_object*)&l_Lake_Toml_atom___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_atom___closed__2 = (const lean_object*)&l_Lake_Toml_atom___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__0_value;
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__1_value;
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "backtrack"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__2 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__2_value;
static const lean_ctor_object l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_0),((lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(3, 24, 51, 215, 74, 174, 135, 90)}};
static const lean_ctor_object l_Lake_Toml_atom_formatter___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_1),((lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 239, 216, 7, 227, 11, 189, 54)}};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__3 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__3_value;
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unexpected syntax '"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__4 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__4_value;
static lean_once_cell_t l_Lake_Toml_atom_formatter___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__5;
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "', expected atom"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__6 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__6_value;
static lean_once_cell_t l_Lake_Toml_atom_formatter___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0_value;
static const lean_string_object l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1_value;
static const lean_ctor_object l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2_value;
static const lean_string_object l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value;
static const lean_closure_object l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value)} };
static const lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4_value;
static lean_once_cell_t l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0_value;
static const lean_closure_object l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value)} };
static const lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1_value;
static lean_once_cell_t l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_sepByLinebreak___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_sepByLinebreak___closed__0;
static const lean_string_object l_Lake_Toml_sepByLinebreak___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lake_Toml_sepByLinebreak___closed__1 = (const lean_object*)&l_Lake_Toml_sepByLinebreak___closed__1_value;
static lean_once_cell_t l_Lake_Toml_sepByLinebreak___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_sepByLinebreak___closed__2;
static lean_once_cell_t l_Lake_Toml_sepByLinebreak___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_sepByLinebreak___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isBinDigit(uint32_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 48;
v___x_3_ = lean_uint32_dec_eq(v_c_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 49;
v___x_5_ = lean_uint32_dec_eq(v_c_1_, v___x_4_);
return v___x_5_;
}
else
{
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object* v_c_6_){
_start:
{
uint32_t v_c_boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_c_boxed_7_ = lean_unbox_uint32(v_c_6_);
lean_dec(v_c_6_);
v_res_8_ = l_Lake_Toml_isBinDigit(v_c_boxed_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isOctDigit(uint32_t v_c_10_){
_start:
{
uint32_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 48;
v___x_12_ = lean_uint32_dec_le(v___x_11_, v_c_10_);
if (v___x_12_ == 0)
{
return v___x_12_;
}
else
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 55;
v___x_14_ = lean_uint32_dec_le(v_c_10_, v___x_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object* v_c_15_){
_start:
{
uint32_t v_c_boxed_16_; uint8_t v_res_17_; lean_object* v_r_18_; 
v_c_boxed_16_ = lean_unbox_uint32(v_c_15_);
lean_dec(v_c_15_);
v_res_17_ = l_Lake_Toml_isOctDigit(v_c_boxed_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isHexDigit(uint32_t v_c_19_){
_start:
{
uint8_t v___y_21_; uint8_t v___y_27_; uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 48;
v___x_33_ = lean_uint32_dec_le(v___x_32_, v_c_19_);
if (v___x_33_ == 0)
{
v___y_27_ = v___x_33_;
goto v___jp_26_;
}
else
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 57;
v___x_35_ = lean_uint32_dec_le(v_c_19_, v___x_34_);
v___y_27_ = v___x_35_;
goto v___jp_26_;
}
v___jp_20_:
{
if (v___y_21_ == 0)
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 65;
v___x_23_ = lean_uint32_dec_le(v___x_22_, v_c_19_);
if (v___x_23_ == 0)
{
return v___x_23_;
}
else
{
uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 70;
v___x_25_ = lean_uint32_dec_le(v_c_19_, v___x_24_);
return v___x_25_;
}
}
else
{
return v___y_21_;
}
}
v___jp_26_:
{
if (v___y_27_ == 0)
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 97;
v___x_29_ = lean_uint32_dec_le(v___x_28_, v_c_19_);
if (v___x_29_ == 0)
{
v___y_21_ = v___x_29_;
goto v___jp_20_;
}
else
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 102;
v___x_31_ = lean_uint32_dec_le(v_c_19_, v___x_30_);
v___y_21_ = v___x_31_;
goto v___jp_20_;
}
}
else
{
return v___y_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object* v_c_36_){
_start:
{
uint32_t v_c_boxed_37_; uint8_t v_res_38_; lean_object* v_r_39_; 
v_c_boxed_37_ = lean_unbox_uint32(v_c_36_);
lean_dec(v_c_36_);
v_res_38_ = l_Lake_Toml_isHexDigit(v_c_boxed_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object* v_s_40_){
_start:
{
lean_inc_ref(v_s_40_);
return v_s_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object* v_s_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lake_Toml_skipFn___redArg(v_s_41_);
lean_dec_ref(v_s_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object* v_x_43_, lean_object* v_s_44_){
_start:
{
lean_inc_ref(v_s_44_);
return v_s_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object* v_x_45_, lean_object* v_s_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lake_Toml_skipFn(v_x_45_, v_s_46_);
lean_dec_ref(v_s_46_);
lean_dec_ref(v_x_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object* v_p_49_, lean_object* v_q_50_, lean_object* v_c_51_, lean_object* v_s_52_){
_start:
{
lean_object* v_s_53_; lean_object* v_errorMsg_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
lean_inc_ref(v_c_51_);
v_s_53_ = lean_apply_2(v_p_49_, v_c_51_, v_s_52_);
v_errorMsg_54_ = lean_ctor_get(v_s_53_, 4);
lean_inc(v_errorMsg_54_);
v___x_55_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_56_ = lean_box(0);
v___x_57_ = l_Option_instBEq_beq___redArg(v___x_55_, v_errorMsg_54_, v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v_c_51_);
lean_dec_ref(v_q_50_);
return v_s_53_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_3(v_q_50_, v___x_58_, v_c_51_, v_s_53_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object* v_f_62_, lean_object* v_c_63_, lean_object* v_s_64_){
_start:
{
lean_object* v_pos_65_; lean_object* v___x_66_; 
v_pos_65_ = lean_ctor_get(v_s_64_, 2);
lean_inc(v_pos_65_);
v___x_66_ = lean_apply_3(v_f_62_, v_pos_65_, v_c_63_, v_s_64_);
return v___x_66_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
if (lean_obj_tag(v_x_68_) == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
lean_dec_ref(v_x_68_);
v___x_70_ = 0;
return v___x_70_;
}
}
else
{
if (lean_obj_tag(v_x_68_) == 0)
{
uint8_t v___x_71_; 
lean_dec_ref(v_x_67_);
v___x_71_ = 0;
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v_val_73_; uint8_t v___x_74_; 
v_val_72_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v_x_67_);
v_val_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_val_73_);
lean_dec_ref(v_x_68_);
v___x_74_ = l_Lean_Parser_instBEqError_beq(v_val_72_, v_val_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_x_75_, v_x_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object* v_p_79_, lean_object* v_c_80_, lean_object* v_s_81_){
_start:
{
lean_object* v_pos_82_; lean_object* v_iniSz_83_; lean_object* v_s_84_; lean_object* v_pos_85_; lean_object* v_errorMsg_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_pos_82_ = lean_ctor_get(v_s_81_, 2);
lean_inc(v_pos_82_);
v_iniSz_83_ = l_Lean_Parser_ParserState_stackSize(v_s_81_);
v_s_84_ = lean_apply_2(v_p_79_, v_c_80_, v_s_81_);
v_pos_85_ = lean_ctor_get(v_s_84_, 2);
lean_inc(v_pos_85_);
v_errorMsg_86_ = lean_ctor_get(v_s_84_, 4);
lean_inc(v_errorMsg_86_);
v___x_87_ = lean_box(0);
v___x_88_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_86_, v___x_87_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_eq(v_pos_85_, v_pos_82_);
lean_dec(v_pos_85_);
if (v___x_89_ == 0)
{
lean_dec(v_iniSz_83_);
lean_dec(v_pos_82_);
return v_s_84_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Parser_ParserState_restore(v_s_84_, v_iniSz_83_, v_pos_82_);
lean_dec(v_iniSz_83_);
return v___x_90_;
}
}
else
{
lean_dec(v_pos_85_);
lean_dec(v_iniSz_83_);
lean_dec(v_pos_82_);
return v_s_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object* v_p_91_, lean_object* v_c_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_zero_95_; uint8_t v_isZero_96_; 
v_zero_95_ = lean_unsigned_to_nat(0u);
v_isZero_96_ = lean_nat_dec_eq(v_x_93_, v_zero_95_);
if (v_isZero_96_ == 1)
{
lean_dec(v_x_93_);
lean_dec_ref(v_c_92_);
lean_dec_ref(v_p_91_);
return v_x_94_;
}
else
{
lean_object* v_s_97_; lean_object* v_errorMsg_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
lean_inc_ref(v_p_91_);
lean_inc_ref(v_c_92_);
v_s_97_ = lean_apply_2(v_p_91_, v_c_92_, v_x_94_);
v_errorMsg_98_ = lean_ctor_get(v_s_97_, 4);
lean_inc(v_errorMsg_98_);
v___x_99_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_100_ = lean_box(0);
v___x_101_ = l_Option_instBEq_beq___redArg(v___x_99_, v_errorMsg_98_, v___x_100_);
if (v___x_101_ == 0)
{
lean_dec(v_x_93_);
lean_dec_ref(v_c_92_);
lean_dec_ref(v_p_91_);
return v_s_97_;
}
else
{
lean_object* v_one_102_; lean_object* v_n_103_; 
v_one_102_ = lean_unsigned_to_nat(1u);
v_n_103_ = lean_nat_sub(v_x_93_, v_one_102_);
lean_dec(v_x_93_);
v_x_93_ = v_n_103_;
v_x_94_ = v_s_97_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object* v_n_105_, lean_object* v_p_106_, lean_object* v_c_107_, lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(v_p_106_, v_c_107_, v_n_105_, v_s_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object* v_s_113_, uint32_t v_c_114_, lean_object* v_expected_115_, uint8_t v_pushMissing_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_117_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__0));
v___x_118_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_119_ = lean_string_push(v___x_118_, v_c_114_);
v___x_120_ = lean_string_append(v___x_117_, v___x_119_);
lean_dec_ref(v___x_119_);
v___x_121_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_122_ = lean_string_append(v___x_120_, v___x_121_);
v___x_123_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_113_, v___x_122_, v_expected_115_, v_pushMissing_116_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object* v_s_124_, lean_object* v_c_125_, lean_object* v_expected_126_, lean_object* v_pushMissing_127_){
_start:
{
uint32_t v_c_boxed_128_; uint8_t v_pushMissing_boxed_129_; lean_object* v_res_130_; 
v_c_boxed_128_ = lean_unbox_uint32(v_c_125_);
lean_dec(v_c_125_);
v_pushMissing_boxed_129_ = lean_unbox(v_pushMissing_127_);
v_res_130_ = l_Lake_Toml_mkUnexpectedCharError(v_s_124_, v_c_boxed_128_, v_expected_126_, v_pushMissing_boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object* v_p_131_, lean_object* v_expected_132_, lean_object* v_c_133_, lean_object* v_s_134_){
_start:
{
lean_object* v_pos_135_; lean_object* v_toInputContext_136_; uint8_t v___x_137_; 
v_pos_135_ = lean_ctor_get(v_s_134_, 2);
v_toInputContext_136_ = lean_ctor_get(v_c_133_, 0);
v___x_137_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_136_, v_pos_135_);
if (v___x_137_ == 0)
{
lean_object* v_inputString_138_; uint32_t v_curr_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_inputString_138_ = lean_ctor_get(v_toInputContext_136_, 0);
v_curr_139_ = lean_string_utf8_get_fast(v_inputString_138_, v_pos_135_);
v___x_140_ = lean_box_uint32(v_curr_139_);
v___x_141_ = lean_apply_1(v_p_131_, v___x_140_);
v___x_142_ = lean_unbox(v___x_141_);
if (v___x_142_ == 0)
{
uint8_t v___x_143_; lean_object* v___x_144_; 
v___x_143_ = 1;
v___x_144_ = l_Lake_Toml_mkUnexpectedCharError(v_s_134_, v_curr_139_, v_expected_132_, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
lean_inc(v_pos_135_);
lean_dec(v_expected_132_);
v___x_145_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_134_, v_c_133_, v_pos_135_);
lean_dec(v_pos_135_);
return v___x_145_;
}
}
else
{
lean_object* v___x_146_; 
lean_dec_ref(v_p_131_);
v___x_146_ = l_Lean_Parser_ParserState_mkEOIError(v_s_134_, v_expected_132_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object* v_p_147_, lean_object* v_expected_148_, lean_object* v_c_149_, lean_object* v_s_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lake_Toml_satisfyFn(v_p_147_, v_expected_148_, v_c_149_, v_s_150_);
lean_dec_ref(v_c_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object* v_p_152_, lean_object* v_expected_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___y_157_; lean_object* v_pos_162_; lean_object* v_toInputContext_163_; uint8_t v___x_164_; 
v_pos_162_ = lean_ctor_get(v_a_155_, 2);
v_toInputContext_163_ = lean_ctor_get(v_a_154_, 0);
v___x_164_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_163_, v_pos_162_);
if (v___x_164_ == 0)
{
lean_object* v_inputString_165_; uint32_t v_curr_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_inputString_165_ = lean_ctor_get(v_toInputContext_163_, 0);
v_curr_166_ = lean_string_utf8_get_fast(v_inputString_165_, v_pos_162_);
v___x_167_ = lean_box_uint32(v_curr_166_);
lean_inc_ref(v_p_152_);
v___x_168_ = lean_apply_1(v_p_152_, v___x_167_);
v___x_169_ = lean_unbox(v___x_168_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; lean_object* v___x_171_; 
v___x_170_ = 1;
v___x_171_ = l_Lake_Toml_mkUnexpectedCharError(v_a_155_, v_curr_166_, v_expected_153_, v___x_170_);
v___y_157_ = v___x_171_;
goto v___jp_156_;
}
else
{
lean_object* v___x_172_; 
lean_inc(v_pos_162_);
lean_dec(v_expected_153_);
v___x_172_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_155_, v_a_154_, v_pos_162_);
lean_dec(v_pos_162_);
v___y_157_ = v___x_172_;
goto v___jp_156_;
}
}
else
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Parser_ParserState_mkEOIError(v_a_155_, v_expected_153_);
v___y_157_ = v___x_173_;
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v_errorMsg_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_errorMsg_158_ = lean_ctor_get(v___y_157_, 4);
v___x_159_ = lean_box(0);
lean_inc(v_errorMsg_158_);
v___x_160_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_p_152_);
return v___y_157_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Parser_takeWhileFn(v_p_152_, v_a_154_, v___y_157_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object* v_p_174_, lean_object* v_expected_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lake_Toml_takeWhile1Fn(v_p_174_, v_expected_175_, v_a_176_, v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object* v_expected_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_pos_182_; lean_object* v_toInputContext_183_; uint8_t v___x_184_; 
v_pos_182_ = lean_ctor_get(v_a_181_, 2);
v_toInputContext_183_ = lean_ctor_get(v_a_180_, 0);
v___x_184_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_183_, v_pos_182_);
if (v___x_184_ == 0)
{
lean_object* v_inputString_185_; uint32_t v_curr_186_; uint8_t v___y_188_; uint32_t v___x_192_; uint8_t v___x_193_; 
v_inputString_185_ = lean_ctor_get(v_toInputContext_183_, 0);
v_curr_186_ = lean_string_utf8_get_fast(v_inputString_185_, v_pos_182_);
v___x_192_ = 48;
v___x_193_ = lean_uint32_dec_le(v___x_192_, v_curr_186_);
if (v___x_193_ == 0)
{
v___y_188_ = v___x_193_;
goto v___jp_187_;
}
else
{
uint32_t v___x_194_; uint8_t v___x_195_; 
v___x_194_ = 57;
v___x_195_ = lean_uint32_dec_le(v_curr_186_, v___x_194_);
v___y_188_ = v___x_195_;
goto v___jp_187_;
}
v___jp_187_:
{
if (v___y_188_ == 0)
{
uint8_t v___x_189_; lean_object* v___x_190_; 
v___x_189_ = 1;
v___x_190_ = l_Lake_Toml_mkUnexpectedCharError(v_a_181_, v_curr_186_, v_expected_179_, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
lean_inc(v_pos_182_);
lean_dec(v_expected_179_);
v___x_191_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_181_, v_a_180_, v_pos_182_);
lean_dec(v_pos_182_);
return v___x_191_;
}
}
}
else
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Parser_ParserState_mkEOIError(v_a_181_, v_expected_179_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object* v_expected_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_Toml_digitFn(v_expected_197_, v_a_198_, v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object* v_expected_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_s_204_; lean_object* v_errorMsg_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
lean_inc(v_expected_201_);
v_s_204_ = l_Lake_Toml_digitFn(v_expected_201_, v_a_202_, v_a_203_);
v_errorMsg_205_ = lean_ctor_get(v_s_204_, 4);
lean_inc(v_errorMsg_205_);
v___x_206_ = lean_box(0);
v___x_207_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v_expected_201_);
return v_s_204_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = l_Lake_Toml_digitFn(v_expected_201_, v_a_202_, v_s_204_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object* v_expected_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lake_Toml_digitPairFn(v_expected_209_, v_a_210_, v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t v_c_213_, lean_object* v_expected_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_pos_217_; lean_object* v_toInputContext_218_; uint8_t v___x_219_; 
v_pos_217_ = lean_ctor_get(v_a_216_, 2);
v_toInputContext_218_ = lean_ctor_get(v_a_215_, 0);
v___x_219_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_218_, v_pos_217_);
if (v___x_219_ == 0)
{
lean_object* v_inputString_220_; uint32_t v_curr_221_; uint8_t v___x_222_; 
v_inputString_220_ = lean_ctor_get(v_toInputContext_218_, 0);
v_curr_221_ = lean_string_utf8_get_fast(v_inputString_220_, v_pos_217_);
v___x_222_ = lean_uint32_dec_eq(v_curr_221_, v_c_213_);
if (v___x_222_ == 0)
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 1;
v___x_224_ = l_Lake_Toml_mkUnexpectedCharError(v_a_216_, v_curr_221_, v_expected_214_, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; 
lean_inc(v_pos_217_);
lean_dec(v_expected_214_);
v___x_225_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_216_, v_a_215_, v_pos_217_);
lean_dec(v_pos_217_);
return v___x_225_;
}
}
else
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Parser_ParserState_mkEOIError(v_a_216_, v_expected_214_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object* v_c_227_, lean_object* v_expected_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
uint32_t v_c_boxed_231_; lean_object* v_res_232_; 
v_c_boxed_231_ = lean_unbox_uint32(v_c_227_);
lean_dec(v_c_227_);
v_res_232_ = l_Lake_Toml_chFn(v_c_boxed_231_, v_expected_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object* v_str_233_, lean_object* v_expected_234_, lean_object* v_strPos_235_, lean_object* v_c_236_, lean_object* v_s_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = lean_string_utf8_at_end(v_str_233_, v_strPos_235_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; lean_object* v_s_240_; lean_object* v_errorMsg_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_239_ = lean_string_utf8_get_fast(v_str_233_, v_strPos_235_);
lean_inc(v_expected_234_);
v_s_240_ = l_Lake_Toml_chFn(v___x_239_, v_expected_234_, v_c_236_, v_s_237_);
v_errorMsg_241_ = lean_ctor_get(v_s_240_, 4);
lean_inc(v_errorMsg_241_);
v___x_242_ = lean_box(0);
v___x_243_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_strPos_235_);
lean_dec(v_expected_234_);
return v_s_240_;
}
else
{
if (v___x_238_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_string_utf8_next_fast(v_str_233_, v_strPos_235_);
lean_dec(v_strPos_235_);
v_strPos_235_ = v___x_244_;
v_s_237_ = v_s_240_;
goto _start;
}
else
{
lean_dec(v_strPos_235_);
lean_dec(v_expected_234_);
return v_s_240_;
}
}
}
else
{
lean_dec(v_strPos_235_);
lean_dec(v_expected_234_);
return v_s_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object* v_str_246_, lean_object* v_expected_247_, lean_object* v_strPos_248_, lean_object* v_c_249_, lean_object* v_s_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_Toml_strAuxFn(v_str_246_, v_expected_247_, v_strPos_248_, v_c_249_, v_s_250_);
lean_dec_ref(v_c_249_);
lean_dec_ref(v_str_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object* v_str_252_, lean_object* v_expected_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_alloc_closure((void*)(l_Lake_Toml_strAuxFn___boxed), 5, 3);
lean_closure_set(v___x_257_, 0, v_str_252_);
lean_closure_set(v___x_257_, 1, v_expected_253_);
lean_closure_set(v___x_257_, 2, v___x_256_);
v___x_258_ = l_Lean_Parser_atomicFn(v___x_257_, v_a_254_, v_a_255_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn(lean_object* v_p_260_, uint32_t v_sep_261_, lean_object* v_expected_262_, lean_object* v_c_263_, lean_object* v_s_264_){
_start:
{
lean_object* v_pos_265_; lean_object* v_toInputContext_266_; uint8_t v___x_267_; 
v_pos_265_ = lean_ctor_get(v_s_264_, 2);
v_toInputContext_266_ = lean_ctor_get(v_c_263_, 0);
v___x_267_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_266_, v_pos_265_);
if (v___x_267_ == 0)
{
lean_object* v_inputString_268_; uint32_t v_curr_269_; lean_object* v_s_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
lean_inc(v_pos_265_);
v_inputString_268_ = lean_ctor_get(v_toInputContext_266_, 0);
v_curr_269_ = lean_string_utf8_get_fast(v_inputString_268_, v_pos_265_);
v_s_270_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_264_, v_c_263_, v_pos_265_);
lean_dec(v_pos_265_);
v___x_271_ = lean_box_uint32(v_curr_269_);
lean_inc_ref(v_p_260_);
v___x_272_ = lean_apply_1(v_p_260_, v___x_271_);
v___x_273_ = lean_unbox(v___x_272_);
if (v___x_273_ == 0)
{
uint8_t v___x_274_; uint8_t v___x_275_; 
lean_dec_ref(v_p_260_);
v___x_274_ = 1;
v___x_275_ = lean_uint32_dec_eq(v_curr_269_, v_sep_261_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
v___x_276_ = l_Lake_Toml_mkUnexpectedCharError(v_s_270_, v_curr_269_, v_expected_262_, v___x_274_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_277_ = ((lean_object*)(l_Lake_Toml_sepByChar1Fn___closed__0));
v___x_278_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_279_ = lean_string_push(v___x_278_, v_curr_269_);
v___x_280_ = lean_string_append(v___x_277_, v___x_279_);
lean_dec_ref(v___x_279_);
v___x_281_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_282_ = lean_string_append(v___x_280_, v___x_281_);
v___x_283_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_270_, v___x_282_, v_expected_262_, v___x_274_);
return v___x_283_;
}
}
else
{
lean_object* v___x_284_; 
v___x_284_ = l_Lake_Toml_sepByChar1AuxFn(v_p_260_, v_sep_261_, v_expected_262_, v_c_263_, v_s_270_);
return v___x_284_;
}
}
else
{
lean_dec(v_expected_262_);
lean_dec_ref(v_p_260_);
return v_s_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object* v_p_285_, uint32_t v_sep_286_, lean_object* v_expected_287_, lean_object* v_c_288_, lean_object* v_s_289_){
_start:
{
lean_object* v_pos_290_; lean_object* v_toInputContext_291_; uint8_t v___x_292_; 
v_pos_290_ = lean_ctor_get(v_s_289_, 2);
v_toInputContext_291_ = lean_ctor_get(v_c_288_, 0);
v___x_292_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_291_, v_pos_290_);
if (v___x_292_ == 0)
{
lean_object* v_inputString_293_; uint32_t v_curr_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_inputString_293_ = lean_ctor_get(v_toInputContext_291_, 0);
v_curr_294_ = lean_string_utf8_get_fast(v_inputString_293_, v_pos_290_);
v___x_295_ = lean_box_uint32(v_curr_294_);
lean_inc_ref(v_p_285_);
v___x_296_ = lean_apply_1(v_p_285_, v___x_295_);
v___x_297_ = lean_unbox(v___x_296_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; 
v___x_298_ = lean_uint32_dec_eq(v_curr_294_, v_sep_286_);
if (v___x_298_ == 0)
{
lean_dec(v_expected_287_);
lean_dec_ref(v_p_285_);
return v_s_289_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_inc(v_pos_290_);
v___x_299_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_289_, v_c_288_, v_pos_290_);
lean_dec(v_pos_290_);
v___x_300_ = l_Lake_Toml_sepByChar1Fn(v_p_285_, v_sep_286_, v_expected_287_, v_c_288_, v___x_299_);
return v___x_300_;
}
}
else
{
lean_object* v___x_301_; 
lean_inc(v_pos_290_);
v___x_301_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_289_, v_c_288_, v_pos_290_);
lean_dec(v_pos_290_);
v_s_289_ = v___x_301_;
goto _start;
}
}
else
{
lean_dec(v_expected_287_);
lean_dec_ref(v_p_285_);
return v_s_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object* v_p_303_, lean_object* v_sep_304_, lean_object* v_expected_305_, lean_object* v_c_306_, lean_object* v_s_307_){
_start:
{
uint32_t v_sep_boxed_308_; lean_object* v_res_309_; 
v_sep_boxed_308_ = lean_unbox_uint32(v_sep_304_);
lean_dec(v_sep_304_);
v_res_309_ = l_Lake_Toml_sepByChar1AuxFn(v_p_303_, v_sep_boxed_308_, v_expected_305_, v_c_306_, v_s_307_);
lean_dec_ref(v_c_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object* v_p_310_, lean_object* v_sep_311_, lean_object* v_expected_312_, lean_object* v_c_313_, lean_object* v_s_314_){
_start:
{
uint32_t v_sep_boxed_315_; lean_object* v_res_316_; 
v_sep_boxed_315_ = lean_unbox_uint32(v_sep_311_);
lean_dec(v_sep_311_);
v_res_316_ = l_Lake_Toml_sepByChar1Fn(v_p_310_, v_sep_boxed_315_, v_expected_312_, v_c_313_, v_s_314_);
lean_dec_ref(v_c_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object* v_startPos_317_, lean_object* v_trailingFn_318_, lean_object* v_c_319_, lean_object* v_s_320_){
_start:
{
lean_object* v_toInputContext_321_; lean_object* v_pos_322_; lean_object* v_inputString_323_; lean_object* v_endPos_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_344_; 
v_toInputContext_321_ = lean_ctor_get(v_c_319_, 0);
lean_inc_ref(v_toInputContext_321_);
v_pos_322_ = lean_ctor_get(v_s_320_, 2);
lean_inc(v_pos_322_);
v_inputString_323_ = lean_ctor_get(v_toInputContext_321_, 0);
v_endPos_324_ = lean_ctor_get(v_toInputContext_321_, 3);
v_isSharedCheck_344_ = !lean_is_exclusive(v_toInputContext_321_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; 
v_unused_345_ = lean_ctor_get(v_toInputContext_321_, 2);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_toInputContext_321_, 1);
lean_dec(v_unused_346_);
v___x_326_ = v_toInputContext_321_;
v_isShared_327_ = v_isSharedCheck_344_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_endPos_324_);
lean_inc(v_inputString_323_);
lean_dec(v_toInputContext_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_344_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_leading_328_; lean_object* v_s_329_; lean_object* v_pos_330_; lean_object* v_val_331_; lean_object* v___y_333_; uint8_t v___x_341_; 
lean_inc(v_startPos_317_);
v_leading_328_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_319_, v_startPos_317_);
v_s_329_ = lean_apply_2(v_trailingFn_318_, v_c_319_, v_s_320_);
v_pos_330_ = lean_ctor_get(v_s_329_, 2);
lean_inc(v_pos_330_);
v_val_331_ = lean_string_utf8_extract(v_inputString_323_, v_startPos_317_, v_pos_322_);
v___x_341_ = lean_nat_dec_le(v_pos_330_, v_endPos_324_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_dec(v_pos_330_);
v___x_342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_342_, 0, v_inputString_323_);
lean_ctor_set(v___x_342_, 1, v_pos_322_);
lean_ctor_set(v___x_342_, 2, v_endPos_324_);
v___y_333_ = v___x_342_;
goto v___jp_332_;
}
else
{
lean_object* v___x_343_; 
lean_dec(v_endPos_324_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_inputString_323_);
lean_ctor_set(v___x_343_, 1, v_pos_322_);
lean_ctor_set(v___x_343_, 2, v_pos_330_);
v___y_333_ = v___x_343_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_334_ = lean_string_utf8_byte_size(v_val_331_);
v___x_335_ = lean_nat_add(v_startPos_317_, v___x_334_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 3, v___x_335_);
lean_ctor_set(v___x_326_, 2, v___y_333_);
lean_ctor_set(v___x_326_, 1, v_startPos_317_);
lean_ctor_set(v___x_326_, 0, v_leading_328_);
v___x_337_ = v___x_326_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_leading_328_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_startPos_317_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v___y_333_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v___x_335_);
v___x_337_ = v_reuseFailAlloc_340_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v_atom_338_; lean_object* v___x_339_; 
v_atom_338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_338_, 0, v___x_337_);
lean_ctor_set(v_atom_338_, 1, v_val_331_);
v___x_339_ = l_Lean_Parser_ParserState_pushSyntax(v_s_329_, v_atom_338_);
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object* v_p_347_, lean_object* v_trailingFn_348_, lean_object* v_c_349_, lean_object* v_s_350_){
_start:
{
lean_object* v_pos_351_; lean_object* v_s_352_; lean_object* v_errorMsg_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_pos_351_ = lean_ctor_get(v_s_350_, 2);
lean_inc(v_pos_351_);
lean_inc_ref(v_c_349_);
v_s_352_ = lean_apply_2(v_p_347_, v_c_349_, v_s_350_);
v_errorMsg_353_ = lean_ctor_get(v_s_352_, 4);
lean_inc(v_errorMsg_353_);
v___x_354_ = lean_box(0);
v___x_355_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec(v_pos_351_);
lean_dec_ref(v_c_349_);
lean_dec_ref(v_trailingFn_348_);
return v_s_352_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = l_Lake_Toml_pushAtom(v_pos_351_, v_trailingFn_348_, v_c_349_, v_s_352_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object* v___y_357_){
_start:
{
lean_inc(v___y_357_);
return v___y_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lake_Toml_atom___lam__0(v___y_358_);
lean_dec(v___y_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object* v___y_360_){
_start:
{
lean_inc_ref(v___y_360_);
return v___y_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lake_Toml_atom___lam__1(v___y_361_);
lean_dec_ref(v___y_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object* v_p_369_, lean_object* v_trailingFn_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_372_ = lean_alloc_closure((void*)(l_Lake_Toml_atomFn), 4, 2);
lean_closure_set(v___x_372_, 0, v_p_369_);
lean_closure_set(v___x_372_, 1, v_trailingFn_370_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_stxTrav_377_; lean_object* v_cur_378_; lean_object* v___x_379_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_stxTrav_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_stxTrav_377_);
lean_dec(v___x_376_);
v_cur_378_ = lean_ctor_get(v_stxTrav_377_, 0);
lean_inc(v_cur_378_);
lean_dec_ref(v_stxTrav_377_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_cur_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_stxTrav_398_; lean_object* v_leadWord_399_; uint8_t v_leadWordIdent_400_; uint8_t v_isUngrouped_401_; uint8_t v_mustBeGrouped_402_; lean_object* v_stack_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v___x_397_ = lean_st_ref_take(v___y_395_);
v_stxTrav_398_ = lean_ctor_get(v___x_397_, 0);
v_leadWord_399_ = lean_ctor_get(v___x_397_, 1);
v_leadWordIdent_400_ = lean_ctor_get_uint8(v___x_397_, sizeof(void*)*3);
v_isUngrouped_401_ = lean_ctor_get_uint8(v___x_397_, sizeof(void*)*3 + 1);
v_mustBeGrouped_402_ = lean_ctor_get_uint8(v___x_397_, sizeof(void*)*3 + 2);
v_stack_403_ = lean_ctor_get(v___x_397_, 2);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_414_ == 0)
{
v___x_405_ = v___x_397_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_stack_403_);
lean_inc(v_leadWord_399_);
lean_inc(v_stxTrav_398_);
lean_dec(v___x_397_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_Lean_Syntax_Traverser_left(v_stxTrav_398_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_leadWord_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_stack_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_413_, sizeof(void*)*3, v_leadWordIdent_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_413_, sizeof(void*)*3 + 1, v_isUngrouped_401_);
lean_ctor_set_uint8(v_reuseFailAlloc_413_, sizeof(void*)*3 + 2, v_mustBeGrouped_402_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_st_ref_set(v___y_395_, v___x_409_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_415_);
lean_dec(v___y_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_419_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* v_cls_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_options_436_; uint8_t v_hasTrace_437_; 
v_options_436_ = lean_ctor_get(v___y_434_, 2);
v_hasTrace_437_ = lean_ctor_get_uint8(v_options_436_, sizeof(void*)*1);
if (v_hasTrace_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_cls_433_);
v___x_438_ = lean_box(v_hasTrace_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v_inheritedTraceOptions_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_inheritedTraceOptions_440_ = lean_ctor_get(v___y_434_, 13);
v___x_441_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_442_ = l_Lean_Name_append(v___x_441_, v_cls_433_);
v___x_443_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_440_, v_options_436_, v___x_442_);
lean_dec(v___x_442_);
v___x_444_ = lean_box(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_446_, v___y_447_);
lean_dec_ref(v___y_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_450_, v___y_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2(v_cls_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_464_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__0);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
lean_ctor_set(v___x_469_, 3, v___x_467_);
lean_ctor_set(v___x_469_, 4, v___x_467_);
lean_ctor_set(v___x_469_, 5, v___x_467_);
lean_ctor_set(v___x_469_, 6, v___x_467_);
lean_ctor_set(v___x_469_, 7, v___x_467_);
lean_ctor_set(v___x_469_, 8, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(32u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4(void){
_start:
{
size_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = ((size_t)5ULL);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_unsigned_to_nat(32u);
v___x_476_ = lean_mk_empty_array_with_capacity(v___x_475_);
v___x_477_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__3);
v___x_478_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
lean_ctor_set(v___x_478_, 2, v___x_474_);
lean_ctor_set(v___x_478_, 3, v___x_474_);
lean_ctor_set_usize(v___x_478_, 4, v___x_473_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_box(1);
v___x_480_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__4);
v___x_481_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__1);
v___x_482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_479_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(lean_object* v_msgData_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; lean_object* v_env_488_; lean_object* v_options_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_487_ = lean_st_ref_get(v___y_485_);
v_env_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc_ref(v_env_488_);
lean_dec(v___x_487_);
v_options_489_ = lean_ctor_get(v___y_484_, 2);
v___x_490_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__2);
v___x_491_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___closed__5);
lean_inc_ref(v_options_489_);
v___x_492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_492_, 0, v_env_488_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
lean_ctor_set(v___x_492_, 2, v___x_491_);
lean_ctor_set(v___x_492_, 3, v_options_489_);
v___x_493_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_msgData_483_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3___boxed(lean_object* v_msgData_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(v_msgData_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_499_;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_500_; double v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_float_of_nat(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(lean_object* v_cls_504_, lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_ref_509_; lean_object* v___x_510_; lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_555_; 
v_ref_509_ = lean_ctor_get(v___y_506_, 5);
v___x_510_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3_spec__3(v_msg_505_, v___y_506_, v___y_507_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_555_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_555_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_555_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v_traceState_516_; lean_object* v_env_517_; lean_object* v_nextMacroScope_518_; lean_object* v_ngen_519_; lean_object* v_auxDeclNGen_520_; lean_object* v_cache_521_; lean_object* v_messages_522_; lean_object* v_infoState_523_; lean_object* v_snapshotTasks_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_554_; 
v___x_515_ = lean_st_ref_take(v___y_507_);
v_traceState_516_ = lean_ctor_get(v___x_515_, 4);
v_env_517_ = lean_ctor_get(v___x_515_, 0);
v_nextMacroScope_518_ = lean_ctor_get(v___x_515_, 1);
v_ngen_519_ = lean_ctor_get(v___x_515_, 2);
v_auxDeclNGen_520_ = lean_ctor_get(v___x_515_, 3);
v_cache_521_ = lean_ctor_get(v___x_515_, 5);
v_messages_522_ = lean_ctor_get(v___x_515_, 6);
v_infoState_523_ = lean_ctor_get(v___x_515_, 7);
v_snapshotTasks_524_ = lean_ctor_get(v___x_515_, 8);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_554_ == 0)
{
v___x_526_ = v___x_515_;
v_isShared_527_ = v_isSharedCheck_554_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snapshotTasks_524_);
lean_inc(v_infoState_523_);
lean_inc(v_messages_522_);
lean_inc(v_cache_521_);
lean_inc(v_traceState_516_);
lean_inc(v_auxDeclNGen_520_);
lean_inc(v_ngen_519_);
lean_inc(v_nextMacroScope_518_);
lean_inc(v_env_517_);
lean_dec(v___x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_554_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint64_t v_tid_528_; lean_object* v_traces_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_553_; 
v_tid_528_ = lean_ctor_get_uint64(v_traceState_516_, sizeof(void*)*1);
v_traces_529_ = lean_ctor_get(v_traceState_516_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_traceState_516_);
if (v_isSharedCheck_553_ == 0)
{
v___x_531_ = v_traceState_516_;
v_isShared_532_ = v_isSharedCheck_553_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_traces_529_);
lean_dec(v_traceState_516_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_553_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; double v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__0);
v___x_535_ = 0;
v___x_536_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_537_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_537_, 0, v_cls_504_);
lean_ctor_set(v___x_537_, 1, v___x_533_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
lean_ctor_set_float(v___x_537_, sizeof(void*)*3, v___x_534_);
lean_ctor_set_float(v___x_537_, sizeof(void*)*3 + 8, v___x_534_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*3 + 16, v___x_535_);
v___x_538_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___closed__1));
v___x_539_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v_a_511_);
lean_ctor_set(v___x_539_, 2, v___x_538_);
lean_inc(v_ref_509_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_ref_509_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_PersistentArray_push___redArg(v_traces_529_, v___x_540_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_541_);
v___x_543_ = v___x_531_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_541_);
lean_ctor_set_uint64(v_reuseFailAlloc_552_, sizeof(void*)*1, v_tid_528_);
v___x_543_ = v_reuseFailAlloc_552_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v___x_543_);
v___x_545_ = v___x_526_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_env_517_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_nextMacroScope_518_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_ngen_519_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_auxDeclNGen_520_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v_cache_521_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_messages_522_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_infoState_523_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_snapshotTasks_524_);
v___x_545_ = v_reuseFailAlloc_551_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_st_ref_set(v___y_507_, v___x_545_);
v___x_547_ = lean_box(0);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_547_);
v___x_549_ = v___x_513_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg___boxed(lean_object* v_cls_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(v_cls_556_, v_msg_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_561_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__4));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__7(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__6));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; lean_object* v_a_581_; 
v___x_580_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_576_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
if (lean_obj_tag(v_a_581_) == 2)
{
lean_object* v_info_582_; lean_object* v_val_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_info_582_ = lean_ctor_get(v_a_581_, 0);
lean_inc(v_info_582_);
v_val_583_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_val_583_);
v___x_584_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_581_);
lean_dec_ref(v_a_581_);
v___x_585_ = 0;
v___x_586_ = lean_box(v___x_585_);
v___x_587_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_587_, 0, v_info_582_);
lean_closure_set(v___x_587_, 1, v_val_583_);
lean_closure_set(v___x_587_, 2, v___x_586_);
v___x_588_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_584_, v___x_587_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v___x_584_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v___x_588_);
v___x_589_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_576_);
return v___x_589_;
}
else
{
return v___x_588_;
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_a_592_; uint8_t v___x_593_; 
v___x_590_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_591_ = l_Lean_isTracingEnabledFor___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_590_, v_a_577_);
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref(v___x_591_);
v___x_593_ = lean_unbox(v_a_592_);
lean_dec(v_a_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec(v_a_581_);
v___x_594_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_595_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__5, &l_Lake_Toml_atom_formatter___redArg___closed__5_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__5);
v___x_596_ = lean_box(0);
v___x_597_ = 0;
v___x_598_ = l_Lean_Syntax_formatStx(v_a_581_, v___x_596_, v___x_597_);
v___x_599_ = l_Lean_MessageData_ofFormat(v___x_598_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_595_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__7, &l_Lake_Toml_atom_formatter___redArg___closed__7_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__7);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(v___x_590_, v___x_602_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; 
lean_dec_ref(v___x_603_);
v___x_604_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_604_;
}
else
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_Toml_atom_formatter___redArg(v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lake_Toml_atom_formatter___redArg(v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lake_Toml_atom_formatter(v_x_619_, v_x_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec_ref(v_x_620_);
lean_dec_ref(v_x_619_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3(lean_object* v_cls_627_, lean_object* v_msg_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___redArg(v_cls_627_, v_msg_628_, v___y_631_, v___y_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3___boxed(lean_object* v_cls_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__3(v_cls_635_, v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_646_);
lean_dec(v_a_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_652_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_657_, v_x_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec_ref(v_x_658_);
lean_dec_ref(v_x_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_665_, lean_object* v_expected_666_, lean_object* v_trailingFn_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_box_uint32(v_c_665_);
v___x_669_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_669_, 0, v___x_668_);
lean_closure_set(v___x_669_, 1, v_expected_666_);
v___x_670_ = l_Lake_Toml_atom(v___x_669_, v_trailingFn_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_671_, lean_object* v_expected_672_, lean_object* v_trailingFn_673_){
_start:
{
uint32_t v_c_boxed_674_; lean_object* v_res_675_; 
v_c_boxed_674_ = lean_unbox_uint32(v_c_671_);
lean_dec(v_c_671_);
v_res_675_ = l_Lake_Toml_chAtom(v_c_boxed_674_, v_expected_672_, v_trailingFn_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
uint8_t v___x_682_; lean_object* v___x_683_; 
v___x_682_ = 0;
v___x_683_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_676_, v___x_682_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
uint32_t v_c_boxed_690_; lean_object* v_res_691_; 
v_c_boxed_690_ = lean_unbox_uint32(v_c_684_);
lean_dec(v_c_684_);
v_res_691_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_690_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_692_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
uint32_t v_c_boxed_709_; lean_object* v_res_710_; 
v_c_boxed_709_ = lean_unbox_uint32(v_c_701_);
lean_dec(v_c_701_);
v_res_710_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_709_, v_x_702_, v_x_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec_ref(v_x_703_);
lean_dec(v_x_702_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_714_);
lean_dec(v_a_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
uint32_t v_x_18__boxed_734_; lean_object* v_res_735_; 
v_x_18__boxed_734_ = lean_unbox_uint32(v_x_726_);
lean_dec(v_x_726_);
v_res_735_ = l_Lake_Toml_chAtom_parenthesizer(v_x_18__boxed_734_, v_x_727_, v_x_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec_ref(v_x_728_);
lean_dec(v_x_727_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_736_, lean_object* v_expected_737_, lean_object* v_trailingFn_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_str_743_; lean_object* v_startInclusive_744_; lean_object* v_endExclusive_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_string_utf8_byte_size(v_s_736_);
v___x_741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_741_, 0, v_s_736_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v___x_740_);
v___x_742_ = l_String_Slice_trimAscii(v___x_741_);
v_str_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_str_743_);
v_startInclusive_744_ = lean_ctor_get(v___x_742_, 1);
lean_inc(v_startInclusive_744_);
v_endExclusive_745_ = lean_ctor_get(v___x_742_, 2);
lean_inc(v_endExclusive_745_);
lean_dec_ref(v___x_742_);
v___x_746_ = lean_string_utf8_extract(v_str_743_, v_startInclusive_744_, v_endExclusive_745_);
lean_dec(v_endExclusive_745_);
lean_dec(v_startInclusive_744_);
lean_dec_ref(v_str_743_);
v___x_747_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_747_, 0, v___x_746_);
lean_closure_set(v___x_747_, 1, v_expected_737_);
v___x_748_ = l_Lake_Toml_atom(v___x_747_, v_trailingFn_738_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_763_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lake_Toml_strAtom_formatter(v_s_772_, v_x_773_, v_x_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_x_774_);
lean_dec(v_x_773_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_784_);
lean_dec(v_a_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_791_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lake_Toml_strAtom_parenthesizer(v_x_796_, v_x_797_, v_x_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec_ref(v_x_798_);
lean_dec(v_x_797_);
lean_dec_ref(v_x_796_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_805_, lean_object* v_startPos_806_, lean_object* v_trailingFn_807_, lean_object* v_c_808_, lean_object* v_s_809_){
_start:
{
lean_object* v_toInputContext_810_; lean_object* v_pos_811_; lean_object* v_inputString_812_; lean_object* v_endPos_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_831_; 
v_toInputContext_810_ = lean_ctor_get(v_c_808_, 0);
lean_inc_ref(v_toInputContext_810_);
v_pos_811_ = lean_ctor_get(v_s_809_, 2);
lean_inc(v_pos_811_);
v_inputString_812_ = lean_ctor_get(v_toInputContext_810_, 0);
v_endPos_813_ = lean_ctor_get(v_toInputContext_810_, 3);
v_isSharedCheck_831_ = !lean_is_exclusive(v_toInputContext_810_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; 
v_unused_832_ = lean_ctor_get(v_toInputContext_810_, 2);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_toInputContext_810_, 1);
lean_dec(v_unused_833_);
v___x_815_ = v_toInputContext_810_;
v_isShared_816_ = v_isSharedCheck_831_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_endPos_813_);
lean_inc(v_inputString_812_);
lean_dec(v_toInputContext_810_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_831_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_leading_817_; lean_object* v_s_818_; lean_object* v_pos_819_; lean_object* v_val_820_; lean_object* v___y_822_; uint8_t v___x_828_; 
lean_inc(v_startPos_806_);
v_leading_817_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_808_, v_startPos_806_);
v_s_818_ = lean_apply_2(v_trailingFn_807_, v_c_808_, v_s_809_);
v_pos_819_ = lean_ctor_get(v_s_818_, 2);
lean_inc(v_pos_819_);
v_val_820_ = lean_string_utf8_extract(v_inputString_812_, v_startPos_806_, v_pos_811_);
v___x_828_ = lean_nat_dec_le(v_pos_819_, v_endPos_813_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_pos_819_);
lean_inc(v_pos_811_);
v___x_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_829_, 0, v_inputString_812_);
lean_ctor_set(v___x_829_, 1, v_pos_811_);
lean_ctor_set(v___x_829_, 2, v_endPos_813_);
v___y_822_ = v___x_829_;
goto v___jp_821_;
}
else
{
lean_object* v___x_830_; 
lean_dec(v_endPos_813_);
lean_inc(v_pos_811_);
v___x_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_830_, 0, v_inputString_812_);
lean_ctor_set(v___x_830_, 1, v_pos_811_);
lean_ctor_set(v___x_830_, 2, v_pos_819_);
v___y_822_ = v___x_830_;
goto v___jp_821_;
}
v___jp_821_:
{
lean_object* v_info_824_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 3, v_pos_811_);
lean_ctor_set(v___x_815_, 2, v___y_822_);
lean_ctor_set(v___x_815_, 1, v_startPos_806_);
lean_ctor_set(v___x_815_, 0, v_leading_817_);
v_info_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_leading_817_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_startPos_806_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v___y_822_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v_pos_811_);
v_info_824_ = v_reuseFailAlloc_827_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = l_Lean_Syntax_mkLit(v_kind_805_, v_val_820_, v_info_824_);
v___x_826_ = l_Lean_Parser_ParserState_pushSyntax(v_s_818_, v___x_825_);
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_834_, lean_object* v_p_835_, lean_object* v_trailingFn_836_, lean_object* v_c_837_, lean_object* v_s_838_){
_start:
{
lean_object* v_pos_839_; lean_object* v_s_840_; lean_object* v_errorMsg_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_pos_839_ = lean_ctor_get(v_s_838_, 2);
lean_inc(v_pos_839_);
lean_inc_ref(v_c_837_);
v_s_840_ = lean_apply_2(v_p_835_, v_c_837_, v_s_838_);
v_errorMsg_841_ = lean_ctor_get(v_s_840_, 4);
lean_inc(v_errorMsg_841_);
v___x_842_ = lean_box(0);
v___x_843_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_dec(v_pos_839_);
lean_dec_ref(v_c_837_);
lean_dec_ref(v_trailingFn_836_);
lean_dec(v_kind_834_);
return v_s_840_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l_Lake_Toml_pushLit(v_kind_834_, v_pos_839_, v_trailingFn_836_, v_c_837_, v_s_840_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_845_, lean_object* v_p_846_, lean_object* v_trailingFn_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_849_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_849_, 0, v_kind_845_);
lean_closure_set(v___x_849_, 1, v_p_846_);
lean_closure_set(v___x_849_, 2, v_trailingFn_847_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lake_Toml_lit_formatter___redArg(v_kind_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_865_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lake_Toml_lit_formatter(v_kind_874_, v_x_875_, v_x_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec_ref(v_x_876_);
lean_dec_ref(v_x_875_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_886_);
lean_dec(v_a_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_893_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lake_Toml_lit_parenthesizer(v_x_898_, v_x_899_, v_x_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec_ref(v_x_900_);
lean_dec_ref(v_x_899_);
lean_dec(v_x_898_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_921_, lean_object* v_kind_922_, uint8_t v_anonymous_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___f_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc(v_kind_922_);
v___f_929_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_929_, 0, v_kind_922_);
v___x_930_ = 0;
v___x_931_ = lean_box(v_anonymous_923_);
v___x_932_ = lean_box(v___x_930_);
v___x_933_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_933_, 0, v_name_921_);
lean_closure_set(v___x_933_, 1, v_kind_922_);
lean_closure_set(v___x_933_, 2, v___x_931_);
lean_closure_set(v___x_933_, 3, v___x_932_);
v___x_934_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_933_, v___f_929_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_935_, lean_object* v_kind_936_, lean_object* v_anonymous_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
uint8_t v_anonymous_boxed_943_; lean_object* v_res_944_; 
v_anonymous_boxed_943_ = lean_unbox(v_anonymous_937_);
v_res_944_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_935_, v_kind_936_, v_anonymous_boxed_943_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_945_, lean_object* v_kind_946_, lean_object* v_p_947_, lean_object* v_trailingFn_948_, uint8_t v_anonymous_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_945_, v_kind_946_, v_anonymous_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_956_, lean_object* v_kind_957_, lean_object* v_p_958_, lean_object* v_trailingFn_959_, lean_object* v_anonymous_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
uint8_t v_anonymous_boxed_966_; lean_object* v_res_967_; 
v_anonymous_boxed_966_ = lean_unbox(v_anonymous_960_);
v_res_967_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_956_, v_kind_957_, v_p_958_, v_trailingFn_959_, v_anonymous_boxed_966_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec_ref(v_trailingFn_959_);
lean_dec_ref(v_p_958_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_969_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_981_, lean_object* v_kind_982_, uint8_t v_anonymous_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___f_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___f_989_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_990_ = 0;
v___x_991_ = lean_box(v_anonymous_983_);
v___x_992_ = lean_box(v___x_990_);
v___x_993_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_993_, 0, v_name_981_);
lean_closure_set(v___x_993_, 1, v_kind_982_);
lean_closure_set(v___x_993_, 2, v___x_991_);
lean_closure_set(v___x_993_, 3, v___x_992_);
v___x_994_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_993_, v___f_989_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_995_, lean_object* v_kind_996_, lean_object* v_anonymous_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
uint8_t v_anonymous_boxed_1003_; lean_object* v_res_1004_; 
v_anonymous_boxed_1003_ = lean_unbox(v_anonymous_997_);
v_res_1004_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_995_, v_kind_996_, v_anonymous_boxed_1003_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_1005_, lean_object* v_kind_1006_, lean_object* v_p_1007_, lean_object* v_trailingFn_1008_, uint8_t v_anonymous_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_1005_, v_kind_1006_, v_anonymous_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_1016_, lean_object* v_kind_1017_, lean_object* v_p_1018_, lean_object* v_trailingFn_1019_, lean_object* v_anonymous_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
uint8_t v_anonymous_boxed_1026_; lean_object* v_res_1027_; 
v_anonymous_boxed_1026_ = lean_unbox(v_anonymous_1020_);
v_res_1027_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_1016_, v_kind_1017_, v_p_1018_, v_trailingFn_1019_, v_anonymous_boxed_1026_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec_ref(v_trailingFn_1019_);
lean_dec_ref(v_p_1018_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1028_, lean_object* v_kind_1029_, lean_object* v_p_1030_, lean_object* v_trailingFn_1031_, uint8_t v_anonymous_1032_){
_start:
{
uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = 0;
lean_inc(v_kind_1029_);
v___x_1034_ = l_Lean_Parser_mkAntiquot(v_name_1028_, v_kind_1029_, v_anonymous_1032_, v___x_1033_);
v___x_1035_ = l_Lake_Toml_lit(v_kind_1029_, v_p_1030_, v_trailingFn_1031_);
v___x_1036_ = l_Lean_Parser_withAntiquot(v___x_1034_, v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1037_, lean_object* v_kind_1038_, lean_object* v_p_1039_, lean_object* v_trailingFn_1040_, lean_object* v_anonymous_1041_){
_start:
{
uint8_t v_anonymous_boxed_1042_; lean_object* v_res_1043_; 
v_anonymous_boxed_1042_ = lean_unbox(v_anonymous_1041_);
v_res_1043_ = l_Lake_Toml_litWithAntiquot(v_name_1037_, v_kind_1038_, v_p_1039_, v_trailingFn_1040_, v_anonymous_boxed_1042_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_Lean_Parser_epsilonInfo;
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_fn_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lake_Toml_epsilon_formatter(v_x_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_x_1059_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec_ref(v_x_1078_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1085_, lean_object* v_x_1086_){
_start:
{
switch(lean_obj_tag(v_x_1086_))
{
case 2:
{
lean_object* v_info_1087_; lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_info_1087_ = lean_ctor_get(v_x_1086_, 0);
v_val_1088_ = lean_ctor_get(v_x_1086_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1086_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v_x_1086_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_inc(v_info_1087_);
lean_dec(v_x_1086_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_apply_1(v_f_1085_, v_info_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_val_1088_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
case 3:
{
lean_object* v_info_1097_; lean_object* v_rawVal_1098_; lean_object* v_val_1099_; lean_object* v_preresolved_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
v_info_1097_ = lean_ctor_get(v_x_1086_, 0);
v_rawVal_1098_ = lean_ctor_get(v_x_1086_, 1);
v_val_1099_ = lean_ctor_get(v_x_1086_, 2);
v_preresolved_1100_ = lean_ctor_get(v_x_1086_, 3);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_1086_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v_x_1086_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_preresolved_1100_);
lean_inc(v_val_1099_);
lean_inc(v_rawVal_1098_);
lean_inc(v_info_1097_);
lean_dec(v_x_1086_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_apply_1(v_f_1085_, v_info_1097_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_rawVal_1098_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_val_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_preresolved_1100_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
case 1:
{
lean_object* v_info_1109_; lean_object* v_kind_1110_; lean_object* v_args_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_info_1109_ = lean_ctor_get(v_x_1086_, 0);
v_kind_1110_ = lean_ctor_get(v_x_1086_, 1);
v_args_1111_ = lean_ctor_get(v_x_1086_, 2);
v___x_1112_ = lean_array_get_size(v_args_1111_);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_sub(v___x_1112_, v___x_1113_);
v___x_1115_ = lean_nat_dec_lt(v___x_1114_, v___x_1112_);
if (v___x_1115_ == 0)
{
lean_dec(v___x_1114_);
lean_dec_ref(v_f_1085_);
return v_x_1086_;
}
else
{
lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1127_; 
lean_inc_ref(v_args_1111_);
lean_inc(v_kind_1110_);
lean_inc(v_info_1109_);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_x_1086_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; 
v_unused_1128_ = lean_ctor_get(v_x_1086_, 2);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_x_1086_, 1);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_x_1086_, 0);
lean_dec(v_unused_1130_);
v___x_1117_ = v_x_1086_;
v_isShared_1118_ = v_isSharedCheck_1127_;
goto v_resetjp_1116_;
}
else
{
lean_dec(v_x_1086_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1127_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_v_1119_; lean_object* v___x_1120_; lean_object* v_xs_x27_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v_v_1119_ = lean_array_fget(v_args_1111_, v___x_1114_);
v___x_1120_ = lean_box(0);
v_xs_x27_1121_ = lean_array_fset(v_args_1111_, v___x_1114_, v___x_1120_);
v___x_1122_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1085_, v_v_1119_);
v___x_1123_ = lean_array_fset(v_xs_x27_1121_, v___x_1114_, v___x_1122_);
lean_dec(v___x_1114_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 2, v___x_1123_);
v___x_1125_ = v___x_1117_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_info_1109_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_kind_1110_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1085_);
return v_x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
lean_object* v_trailing_1133_; lean_object* v_leading_1134_; lean_object* v_pos_1135_; lean_object* v_endPos_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1153_; 
v_trailing_1133_ = lean_ctor_get(v_x_1132_, 2);
v_leading_1134_ = lean_ctor_get(v_x_1132_, 0);
v_pos_1135_ = lean_ctor_get(v_x_1132_, 1);
v_endPos_1136_ = lean_ctor_get(v_x_1132_, 3);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1138_ = v_x_1132_;
v_isShared_1139_ = v_isSharedCheck_1153_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_endPos_1136_);
lean_inc(v_trailing_1133_);
lean_inc(v_pos_1135_);
lean_inc(v_leading_1134_);
lean_dec(v_x_1132_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1153_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_str_1140_; lean_object* v_startPos_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1151_; 
v_str_1140_ = lean_ctor_get(v_trailing_1133_, 0);
v_startPos_1141_ = lean_ctor_get(v_trailing_1133_, 1);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_trailing_1133_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_trailing_1133_, 2);
lean_dec(v_unused_1152_);
v___x_1143_ = v_trailing_1133_;
v_isShared_1144_ = v_isSharedCheck_1151_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_startPos_1141_);
lean_inc(v_str_1140_);
lean_dec(v_trailing_1133_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1151_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 2, v_stopPos_1131_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_str_1140_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_startPos_1141_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_stopPos_1131_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 2, v___x_1146_);
v___x_1148_ = v___x_1138_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_leading_1134_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_pos_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_endPos_1136_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
else
{
lean_dec(v_stopPos_1131_);
return v_x_1132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1154_, lean_object* v_x_1155_){
_start:
{
switch(lean_obj_tag(v_x_1155_))
{
case 2:
{
lean_object* v_info_1156_; lean_object* v_val_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_info_1156_ = lean_ctor_get(v_x_1155_, 0);
v_val_1157_ = lean_ctor_get(v_x_1155_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v_x_1155_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_val_1157_);
lean_inc(v_info_1156_);
lean_dec(v_x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1154_, v_info_1156_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_val_1157_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
case 3:
{
lean_object* v_info_1166_; lean_object* v_rawVal_1167_; lean_object* v_val_1168_; lean_object* v_preresolved_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1177_; 
v_info_1166_ = lean_ctor_get(v_x_1155_, 0);
v_rawVal_1167_ = lean_ctor_get(v_x_1155_, 1);
v_val_1168_ = lean_ctor_get(v_x_1155_, 2);
v_preresolved_1169_ = lean_ctor_get(v_x_1155_, 3);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1171_ = v_x_1155_;
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_preresolved_1169_);
lean_inc(v_val_1168_);
lean_inc(v_rawVal_1167_);
lean_inc(v_info_1166_);
lean_dec(v_x_1155_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1154_, v_info_1166_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_rawVal_1167_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_val_1168_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_preresolved_1169_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
case 1:
{
lean_object* v_info_1178_; lean_object* v_kind_1179_; lean_object* v_args_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_info_1178_ = lean_ctor_get(v_x_1155_, 0);
v_kind_1179_ = lean_ctor_get(v_x_1155_, 1);
v_args_1180_ = lean_ctor_get(v_x_1155_, 2);
v___x_1181_ = lean_array_get_size(v_args_1180_);
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_nat_sub(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_nat_dec_lt(v___x_1183_, v___x_1181_);
if (v___x_1184_ == 0)
{
lean_dec(v___x_1183_);
lean_dec(v_stopPos_1154_);
return v_x_1155_;
}
else
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1196_; 
lean_inc_ref(v_args_1180_);
lean_inc(v_kind_1179_);
lean_inc(v_info_1178_);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; lean_object* v_unused_1198_; lean_object* v_unused_1199_; 
v_unused_1197_ = lean_ctor_get(v_x_1155_, 2);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_x_1155_, 1);
lean_dec(v_unused_1198_);
v_unused_1199_ = lean_ctor_get(v_x_1155_, 0);
lean_dec(v_unused_1199_);
v___x_1186_ = v_x_1155_;
v_isShared_1187_ = v_isSharedCheck_1196_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_x_1155_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1196_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_v_1188_; lean_object* v___x_1189_; lean_object* v_xs_x27_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_v_1188_ = lean_array_fget(v_args_1180_, v___x_1183_);
v___x_1189_ = lean_box(0);
v_xs_x27_1190_ = lean_array_fset(v_args_1180_, v___x_1183_, v___x_1189_);
v___x_1191_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1154_, v_v_1188_);
v___x_1192_ = lean_array_fset(v_xs_x27_1190_, v___x_1183_, v___x_1191_);
lean_dec(v___x_1183_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 2, v___x_1192_);
v___x_1194_ = v___x_1186_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_info_1178_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_kind_1179_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1154_);
return v_x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1200_, lean_object* v_c_1201_, lean_object* v_s_1202_){
_start:
{
lean_object* v_s_1203_; lean_object* v_stxStack_1204_; lean_object* v_pos_1205_; lean_object* v_tail_1206_; lean_object* v_s_1207_; lean_object* v_tail_1208_; lean_object* v___x_1209_; 
v_s_1203_ = lean_apply_2(v_p_1200_, v_c_1201_, v_s_1202_);
v_stxStack_1204_ = lean_ctor_get(v_s_1203_, 0);
lean_inc_ref(v_stxStack_1204_);
v_pos_1205_ = lean_ctor_get(v_s_1203_, 2);
lean_inc(v_pos_1205_);
v_tail_1206_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1204_);
lean_dec_ref(v_stxStack_1204_);
v_s_1207_ = l_Lean_Parser_ParserState_popSyntax(v_s_1203_);
v_tail_1208_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1205_, v_tail_1206_);
v___x_1209_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1207_, v_tail_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lake_Toml_trailing_formatter(v_p_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec_ref(v_p_1221_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lake_Toml_trailing_parenthesizer(v_p_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_p_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1247_, 0, v_p_1246_);
v___x_1248_ = l_Lean_Parser_epsilonInfo;
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_p_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___x_1258_; lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1254_);
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = l_Lean_Syntax_getKind(v_a_1259_);
v___x_1261_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1260_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lake_Toml_dynamicNode_formatter(v_x_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec_ref(v_x_1275_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v_stxTrav_1285_; lean_object* v_cur_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_st_ref_get(v___y_1282_);
v_stxTrav_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc_ref(v_stxTrav_1285_);
lean_dec(v___x_1284_);
v_cur_1286_ = lean_ctor_get(v_stxTrav_1285_, 0);
lean_inc(v_cur_1286_);
lean_dec_ref(v_stxTrav_1285_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_cur_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1288_);
lean_dec(v___y_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1292_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1304_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = l_Lean_Syntax_getKind(v_a_1309_);
v___x_1311_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1310_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec_ref(v_x_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_fn_1338_; lean_object* v___x_1339_; 
lean_inc_ref(v_f_1332_);
v___x_1335_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1335_, 0, v_f_1332_);
v___x_1336_ = l_Lake_Toml_dynamicNode(v___x_1335_);
v___x_1337_ = lean_apply_1(v_f_1332_, v___x_1336_);
v_fn_1338_ = lean_ctor_get(v___x_1337_, 1);
lean_inc_ref(v_fn_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = lean_apply_2(v_fn_1338_, v_a_1333_, v_a_1334_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lake_Toml_recNode_formatter(v_f_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec_ref(v_f_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lake_Toml_recNode_parenthesizer(v_f_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec_ref(v_f_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1393_, 0, v_f_1392_);
v___x_1394_ = l_Lake_Toml_dynamicNode(v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1395_, lean_object* v_kind_1396_, lean_object* v_f_1397_, uint8_t v_anonymous_1398_, lean_object* v_p_1399_){
_start:
{
uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1400_ = 1;
lean_inc(v_kind_1396_);
v___x_1401_ = l_Lean_Parser_mkAntiquot(v_name_1395_, v_kind_1396_, v_anonymous_1398_, v___x_1400_);
v___x_1402_ = lean_apply_1(v_f_1397_, v_p_1399_);
v___x_1403_ = l_Lean_Parser_withAntiquot(v___x_1401_, v___x_1402_);
v___x_1404_ = l_Lean_Parser_withCache(v_kind_1396_, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1405_, lean_object* v_kind_1406_, lean_object* v_f_1407_, lean_object* v_anonymous_1408_, lean_object* v_p_1409_){
_start:
{
uint8_t v_anonymous_boxed_1410_; lean_object* v_res_1411_; 
v_anonymous_boxed_1410_ = lean_unbox(v_anonymous_1408_);
v_res_1411_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1405_, v_kind_1406_, v_f_1407_, v_anonymous_boxed_1410_, v_p_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1412_, lean_object* v_kind_1413_, lean_object* v_f_1414_, uint8_t v_anonymous_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1421_ = 1;
v___x_1422_ = lean_box(v_anonymous_1415_);
v___x_1423_ = lean_box(v___x_1421_);
lean_inc(v_kind_1413_);
lean_inc_ref(v_name_1412_);
v___x_1424_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1424_, 0, v_name_1412_);
lean_closure_set(v___x_1424_, 1, v_kind_1413_);
lean_closure_set(v___x_1424_, 2, v___x_1422_);
lean_closure_set(v___x_1424_, 3, v___x_1423_);
v___x_1425_ = lean_box(v_anonymous_1415_);
v___x_1426_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1426_, 0, v_name_1412_);
lean_closure_set(v___x_1426_, 1, v_kind_1413_);
lean_closure_set(v___x_1426_, 2, v_f_1414_);
lean_closure_set(v___x_1426_, 3, v___x_1425_);
v___x_1427_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1427_, 0, v___x_1426_);
v___x_1428_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1424_, v___x_1427_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1429_, lean_object* v_kind_1430_, lean_object* v_f_1431_, lean_object* v_anonymous_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
uint8_t v_anonymous_boxed_1438_; lean_object* v_res_1439_; 
v_anonymous_boxed_1438_ = lean_unbox(v_anonymous_1432_);
v_res_1439_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1429_, v_kind_1430_, v_f_1431_, v_anonymous_boxed_1438_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1440_, lean_object* v_kind_1441_, lean_object* v_f_1442_, uint8_t v_anonymous_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1449_ = 1;
v___x_1450_ = lean_box(v_anonymous_1443_);
v___x_1451_ = lean_box(v___x_1449_);
lean_inc(v_kind_1441_);
lean_inc_ref(v_name_1440_);
v___x_1452_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1452_, 0, v_name_1440_);
lean_closure_set(v___x_1452_, 1, v_kind_1441_);
lean_closure_set(v___x_1452_, 2, v___x_1450_);
lean_closure_set(v___x_1452_, 3, v___x_1451_);
v___x_1453_ = lean_box(v_anonymous_1443_);
v___x_1454_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1454_, 0, v_name_1440_);
lean_closure_set(v___x_1454_, 1, v_kind_1441_);
lean_closure_set(v___x_1454_, 2, v_f_1442_);
lean_closure_set(v___x_1454_, 3, v___x_1453_);
v___x_1455_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1455_, 0, v___x_1454_);
v___x_1456_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1452_, v___x_1455_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1457_, lean_object* v_kind_1458_, lean_object* v_f_1459_, lean_object* v_anonymous_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
uint8_t v_anonymous_boxed_1466_; lean_object* v_res_1467_; 
v_anonymous_boxed_1466_ = lean_unbox(v_anonymous_1460_);
v_res_1467_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1457_, v_kind_1458_, v_f_1459_, v_anonymous_boxed_1466_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1468_, lean_object* v_kind_1469_, lean_object* v_f_1470_, uint8_t v_anonymous_1471_){
_start:
{
uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1472_ = 1;
lean_inc(v_kind_1469_);
lean_inc_ref(v_name_1468_);
v___x_1473_ = l_Lean_Parser_mkAntiquot(v_name_1468_, v_kind_1469_, v_anonymous_1471_, v___x_1472_);
v___x_1474_ = lean_box(v_anonymous_1471_);
lean_inc(v_kind_1469_);
v___x_1475_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1475_, 0, v_name_1468_);
lean_closure_set(v___x_1475_, 1, v_kind_1469_);
lean_closure_set(v___x_1475_, 2, v_f_1470_);
lean_closure_set(v___x_1475_, 3, v___x_1474_);
v___x_1476_ = l_Lake_Toml_recNode(v___x_1475_);
v___x_1477_ = l_Lean_Parser_withAntiquot(v___x_1473_, v___x_1476_);
v___x_1478_ = l_Lean_Parser_withCache(v_kind_1469_, v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1479_, lean_object* v_kind_1480_, lean_object* v_f_1481_, lean_object* v_anonymous_1482_){
_start:
{
uint8_t v_anonymous_boxed_1483_; lean_object* v_res_1484_; 
v_anonymous_boxed_1483_ = lean_unbox(v_anonymous_1482_);
v_res_1484_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1479_, v_kind_1480_, v_f_1481_, v_anonymous_boxed_1483_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___f_1492_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1493_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1494_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1494_, 0, v___x_1493_);
lean_closure_set(v___x_1494_, 1, v___f_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1502_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1503_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1503_, 0, v___x_1501_);
lean_closure_set(v___x_1503_, 1, v_p_1495_);
lean_closure_set(v___x_1503_, 2, v___x_1502_);
v___x_1504_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1505_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1503_, v___x_1504_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1513_, uint8_t v_allowTrailingLinebreak_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1513_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1521_, lean_object* v_allowTrailingLinebreak_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1528_; lean_object* v_res_1529_; 
v_allowTrailingLinebreak_boxed_1528_ = lean_unbox(v_allowTrailingLinebreak_1522_);
v_res_1529_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1521_, v_allowTrailingLinebreak_boxed_1528_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1529_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___f_1533_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1534_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1535_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1535_, 0, v___x_1534_);
lean_closure_set(v___x_1535_, 1, v___f_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1542_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1543_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1544_, 0, v___x_1542_);
lean_closure_set(v___x_1544_, 1, v_p_1536_);
lean_closure_set(v___x_1544_, 2, v___x_1543_);
v___x_1545_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1546_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1544_, v___x_1545_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1554_, uint8_t v_allowTrailingLinebreak_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1554_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1562_, lean_object* v_allowTrailingLinebreak_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1569_; lean_object* v_res_1570_; 
v_allowTrailingLinebreak_boxed_1569_ = lean_unbox(v_allowTrailingLinebreak_1563_);
v_res_1570_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1562_, v_allowTrailingLinebreak_boxed_1569_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
return v_res_1570_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1572_ = l_Lean_Parser_symbol(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1575_ = l_Lean_Parser_checkLinebreakBefore(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = l_Lean_Parser_pushNone;
v___x_1577_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1578_ = l_Lean_Parser_andthen(v___x_1577_, v___x_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1579_, uint8_t v_allowTrailingLinebreak_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_p_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1581_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1582_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1583_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1581_, v_p_1579_, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1585_ = l_Lean_Parser_sepByNoAntiquot(v_p_1583_, v___x_1584_, v_allowTrailingLinebreak_1580_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1586_, lean_object* v_allowTrailingLinebreak_1587_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1588_; lean_object* v_res_1589_; 
v_allowTrailingLinebreak_boxed_1588_ = lean_unbox(v_allowTrailingLinebreak_1587_);
v_res_1589_ = l_Lake_Toml_sepByLinebreak(v_p_1586_, v_allowTrailingLinebreak_boxed_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1596_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1597_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1598_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1598_, 0, v___x_1596_);
lean_closure_set(v___x_1598_, 1, v_p_1590_);
lean_closure_set(v___x_1598_, 2, v___x_1597_);
v___x_1599_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1600_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1598_, v___x_1599_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1608_, uint8_t v_allowTrailingLinebreak_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1608_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1616_, lean_object* v_allowTrailingLinebreak_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1623_; lean_object* v_res_1624_; 
v_allowTrailingLinebreak_boxed_1623_ = lean_unbox(v_allowTrailingLinebreak_1617_);
v_res_1624_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1616_, v_allowTrailingLinebreak_boxed_1623_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1631_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1632_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1633_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1633_, 0, v___x_1631_);
lean_closure_set(v___x_1633_, 1, v_p_1625_);
lean_closure_set(v___x_1633_, 2, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1635_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1633_, v___x_1634_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1643_, uint8_t v_allowTrailingLinebreak_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1643_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1651_, lean_object* v_allowTrailingLinebreak_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1658_; lean_object* v_res_1659_; 
v_allowTrailingLinebreak_boxed_1658_ = lean_unbox(v_allowTrailingLinebreak_1652_);
v_res_1659_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1651_, v_allowTrailingLinebreak_boxed_1658_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1660_, uint8_t v_allowTrailingLinebreak_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v_p_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1662_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1663_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1664_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1662_, v_p_1660_, v___x_1663_);
v___x_1665_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1666_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1664_, v___x_1665_, v_allowTrailingLinebreak_1661_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1667_, lean_object* v_allowTrailingLinebreak_1668_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1669_; lean_object* v_res_1670_; 
v_allowTrailingLinebreak_boxed_1669_ = lean_unbox(v_allowTrailingLinebreak_1668_);
v_res_1670_ = l_Lake_Toml_sepBy1Linebreak(v_p_1667_, v_allowTrailingLinebreak_boxed_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1671_, lean_object* v_c_1672_, lean_object* v_s_1673_){
_start:
{
lean_object* v_toCacheableParserContext_1674_; lean_object* v_quotDepth_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_toCacheableParserContext_1674_ = lean_ctor_get(v_c_1672_, 2);
v_quotDepth_1675_ = lean_ctor_get(v_toCacheableParserContext_1674_, 1);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_nat_dec_lt(v___x_1676_, v_quotDepth_1675_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_apply_2(v_p_1671_, v_c_1672_, v_s_1673_);
return v___x_1678_;
}
else
{
lean_dec_ref(v_c_1672_);
lean_dec_ref(v_p_1671_);
return v_s_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; 
lean_inc(v_a_1683_);
lean_inc_ref(v_a_1682_);
lean_inc(v_a_1681_);
lean_inc_ref(v_a_1680_);
v___x_1685_ = lean_apply_5(v_p_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, lean_box(0));
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
lean_inc(v_a_1697_);
lean_inc_ref(v_a_1696_);
lean_inc(v_a_1695_);
lean_inc_ref(v_a_1694_);
v___x_1699_ = lean_apply_5(v_p_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, lean_box(0));
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1707_){
_start:
{
lean_object* v_info_1708_; lean_object* v_fn_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_info_1708_ = lean_ctor_get(v_p_1707_, 0);
v_fn_1709_ = lean_ctor_get(v_p_1707_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_p_1707_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1711_ = v_p_1707_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_fn_1709_);
lean_inc(v_info_1708_);
lean_dec(v_p_1707_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1713_, 0, v_fn_1709_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_info_1708_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_ParserUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_ParserUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lake_Toml_ParserUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_ParserUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_ParserUtil(builtin);
}
#ifdef __cplusplus
}
#endif
