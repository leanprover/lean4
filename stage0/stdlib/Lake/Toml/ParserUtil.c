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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__4 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__4_value;
static const lean_ctor_object l_Lake_Toml_atom_formatter___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__5 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__5_value;
static lean_once_cell_t l_Lake_Toml_atom_formatter___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__6;
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unexpected syntax '"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__7 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__7_value;
static lean_once_cell_t l_Lake_Toml_atom_formatter___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__8;
static const lean_string_object l_Lake_Toml_atom_formatter___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "', expected atom"};
static const lean_object* l_Lake_Toml_atom_formatter___redArg___closed__9 = (const lean_object*)&l_Lake_Toml_atom_formatter___redArg___closed__9_value;
static lean_once_cell_t l_Lake_Toml_atom_formatter___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_atom_formatter___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 48;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v_c_19_);
if (v___x_31_ == 0)
{
goto v___jp_25_;
}
else
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 57;
v___x_33_ = lean_uint32_dec_le(v_c_19_, v___x_32_);
if (v___x_33_ == 0)
{
goto v___jp_25_;
}
else
{
return v___x_33_;
}
}
v___jp_20_:
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 65;
v___x_22_ = lean_uint32_dec_le(v___x_21_, v_c_19_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 70;
v___x_24_ = lean_uint32_dec_le(v_c_19_, v___x_23_);
return v___x_24_;
}
}
v___jp_25_:
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 97;
v___x_27_ = lean_uint32_dec_le(v___x_26_, v_c_19_);
if (v___x_27_ == 0)
{
goto v___jp_20_;
}
else
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 102;
v___x_29_ = lean_uint32_dec_le(v_c_19_, v___x_28_);
if (v___x_29_ == 0)
{
goto v___jp_20_;
}
else
{
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object* v_c_34_){
_start:
{
uint32_t v_c_boxed_35_; uint8_t v_res_36_; lean_object* v_r_37_; 
v_c_boxed_35_ = lean_unbox_uint32(v_c_34_);
lean_dec(v_c_34_);
v_res_36_ = l_Lake_Toml_isHexDigit(v_c_boxed_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object* v_s_38_){
_start:
{
lean_inc_ref(v_s_38_);
return v_s_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object* v_s_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_Toml_skipFn___redArg(v_s_39_);
lean_dec_ref(v_s_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object* v_x_41_, lean_object* v_s_42_){
_start:
{
lean_inc_ref(v_s_42_);
return v_s_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object* v_x_43_, lean_object* v_s_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_Toml_skipFn(v_x_43_, v_s_44_);
lean_dec_ref(v_s_44_);
lean_dec_ref(v_x_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object* v_p_47_, lean_object* v_q_48_, lean_object* v_c_49_, lean_object* v_s_50_){
_start:
{
lean_object* v_s_51_; lean_object* v_errorMsg_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
lean_inc_ref(v_c_49_);
v_s_51_ = lean_apply_2(v_p_47_, v_c_49_, v_s_50_);
v_errorMsg_52_ = lean_ctor_get(v_s_51_, 4);
lean_inc(v_errorMsg_52_);
v___x_53_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_54_ = lean_box(0);
v___x_55_ = l_Option_instBEq_beq___redArg(v___x_53_, v_errorMsg_52_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v_c_49_);
lean_dec_ref(v_q_48_);
return v_s_51_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_box(0);
v___x_57_ = lean_apply_3(v_q_48_, v___x_56_, v_c_49_, v_s_51_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object* v_f_60_, lean_object* v_c_61_, lean_object* v_s_62_){
_start:
{
lean_object* v_pos_63_; lean_object* v___x_64_; 
v_pos_63_ = lean_ctor_get(v_s_62_, 2);
lean_inc(v_pos_63_);
v___x_64_ = lean_apply_3(v_f_60_, v_pos_63_, v_c_61_, v_s_62_);
return v___x_64_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
if (lean_obj_tag(v_x_66_) == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 1;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
else
{
if (lean_obj_tag(v_x_66_) == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v_val_71_; uint8_t v___x_72_; 
v_val_70_ = lean_ctor_get(v_x_65_, 0);
v_val_71_ = lean_ctor_get(v_x_66_, 0);
v___x_72_ = l_Lean_Parser_instBEqError_beq(v_val_70_, v_val_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_x_73_, v_x_74_);
lean_dec(v_x_74_);
lean_dec(v_x_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object* v_p_77_, lean_object* v_c_78_, lean_object* v_s_79_){
_start:
{
lean_object* v_pos_80_; lean_object* v_iniSz_81_; lean_object* v_s_82_; lean_object* v_pos_83_; lean_object* v_errorMsg_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_pos_80_ = lean_ctor_get(v_s_79_, 2);
lean_inc(v_pos_80_);
v_iniSz_81_ = l_Lean_Parser_ParserState_stackSize(v_s_79_);
v_s_82_ = lean_apply_2(v_p_77_, v_c_78_, v_s_79_);
v_pos_83_ = lean_ctor_get(v_s_82_, 2);
lean_inc(v_pos_83_);
v_errorMsg_84_ = lean_ctor_get(v_s_82_, 4);
lean_inc(v_errorMsg_84_);
v___x_85_ = lean_box(0);
v___x_86_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_84_, v___x_85_);
lean_dec(v_errorMsg_84_);
if (v___x_86_ == 0)
{
uint8_t v_decide_87_; 
v_decide_87_ = lean_nat_dec_eq(v_pos_83_, v_pos_80_);
lean_dec(v_pos_83_);
if (v_decide_87_ == 0)
{
lean_dec(v_iniSz_81_);
lean_dec(v_pos_80_);
return v_s_82_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Parser_ParserState_restore(v_s_82_, v_iniSz_81_, v_pos_80_);
lean_dec(v_iniSz_81_);
return v___x_88_;
}
}
else
{
lean_dec(v_pos_83_);
lean_dec(v_iniSz_81_);
lean_dec(v_pos_80_);
return v_s_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object* v_p_89_, lean_object* v_c_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_zero_93_; uint8_t v_isZero_94_; 
v_zero_93_ = lean_unsigned_to_nat(0u);
v_isZero_94_ = lean_nat_dec_eq(v_x_91_, v_zero_93_);
if (v_isZero_94_ == 1)
{
lean_dec(v_x_91_);
lean_dec_ref(v_c_90_);
lean_dec_ref(v_p_89_);
return v_x_92_;
}
else
{
lean_object* v_s_95_; lean_object* v_errorMsg_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
lean_inc_ref(v_p_89_);
lean_inc_ref(v_c_90_);
v_s_95_ = lean_apply_2(v_p_89_, v_c_90_, v_x_92_);
v_errorMsg_96_ = lean_ctor_get(v_s_95_, 4);
lean_inc(v_errorMsg_96_);
v___x_97_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_98_ = lean_box(0);
v___x_99_ = l_Option_instBEq_beq___redArg(v___x_97_, v_errorMsg_96_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec(v_x_91_);
lean_dec_ref(v_c_90_);
lean_dec_ref(v_p_89_);
return v_s_95_;
}
else
{
lean_object* v_one_100_; lean_object* v_n_101_; 
v_one_100_ = lean_unsigned_to_nat(1u);
v_n_101_ = lean_nat_sub(v_x_91_, v_one_100_);
lean_dec(v_x_91_);
v_x_91_ = v_n_101_;
v_x_92_ = v_s_95_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object* v_n_103_, lean_object* v_p_104_, lean_object* v_c_105_, lean_object* v_s_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(v_p_104_, v_c_105_, v_n_103_, v_s_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object* v_s_111_, uint32_t v_c_112_, lean_object* v_expected_113_, uint8_t v_pushMissing_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_115_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__0));
v___x_116_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_117_ = lean_string_push(v___x_116_, v_c_112_);
v___x_118_ = lean_string_append(v___x_115_, v___x_117_);
lean_dec_ref(v___x_117_);
v___x_119_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_120_ = lean_string_append(v___x_118_, v___x_119_);
v___x_121_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_111_, v___x_120_, v_expected_113_, v_pushMissing_114_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object* v_s_122_, lean_object* v_c_123_, lean_object* v_expected_124_, lean_object* v_pushMissing_125_){
_start:
{
uint32_t v_c_boxed_126_; uint8_t v_pushMissing_boxed_127_; lean_object* v_res_128_; 
v_c_boxed_126_ = lean_unbox_uint32(v_c_123_);
lean_dec(v_c_123_);
v_pushMissing_boxed_127_ = lean_unbox(v_pushMissing_125_);
v_res_128_ = l_Lake_Toml_mkUnexpectedCharError(v_s_122_, v_c_boxed_126_, v_expected_124_, v_pushMissing_boxed_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object* v_p_129_, lean_object* v_expected_130_, lean_object* v_c_131_, lean_object* v_s_132_){
_start:
{
lean_object* v_pos_133_; lean_object* v_toInputContext_134_; uint8_t v___x_135_; 
v_pos_133_ = lean_ctor_get(v_s_132_, 2);
v_toInputContext_134_ = lean_ctor_get(v_c_131_, 0);
v___x_135_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_134_, v_pos_133_);
if (v___x_135_ == 0)
{
lean_object* v_inputString_136_; uint32_t v_curr_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_inputString_136_ = lean_ctor_get(v_toInputContext_134_, 0);
v_curr_137_ = lean_string_utf8_get_fast(v_inputString_136_, v_pos_133_);
v___x_138_ = lean_box_uint32(v_curr_137_);
v___x_139_ = lean_apply_1(v_p_129_, v___x_138_);
v___x_140_ = lean_unbox(v___x_139_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; lean_object* v___x_142_; 
v___x_141_ = 1;
v___x_142_ = l_Lake_Toml_mkUnexpectedCharError(v_s_132_, v_curr_137_, v_expected_130_, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
lean_inc(v_pos_133_);
lean_dec(v_expected_130_);
v___x_143_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_132_, v_c_131_, v_pos_133_);
lean_dec(v_pos_133_);
return v___x_143_;
}
}
else
{
lean_object* v___x_144_; 
lean_dec_ref(v_p_129_);
v___x_144_ = l_Lean_Parser_ParserState_mkEOIError(v_s_132_, v_expected_130_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object* v_p_145_, lean_object* v_expected_146_, lean_object* v_c_147_, lean_object* v_s_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lake_Toml_satisfyFn(v_p_145_, v_expected_146_, v_c_147_, v_s_148_);
lean_dec_ref(v_c_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object* v_p_150_, lean_object* v_expected_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___y_155_; lean_object* v_pos_160_; lean_object* v_toInputContext_161_; uint8_t v___x_162_; 
v_pos_160_ = lean_ctor_get(v_a_153_, 2);
v_toInputContext_161_ = lean_ctor_get(v_a_152_, 0);
v___x_162_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_161_, v_pos_160_);
if (v___x_162_ == 0)
{
lean_object* v_inputString_163_; uint32_t v_curr_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_inputString_163_ = lean_ctor_get(v_toInputContext_161_, 0);
v_curr_164_ = lean_string_utf8_get_fast(v_inputString_163_, v_pos_160_);
v___x_165_ = lean_box_uint32(v_curr_164_);
lean_inc_ref(v_p_150_);
v___x_166_ = lean_apply_1(v_p_150_, v___x_165_);
v___x_167_ = lean_unbox(v___x_166_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; lean_object* v___x_169_; 
v___x_168_ = 1;
v___x_169_ = l_Lake_Toml_mkUnexpectedCharError(v_a_153_, v_curr_164_, v_expected_151_, v___x_168_);
v___y_155_ = v___x_169_;
goto v___jp_154_;
}
else
{
lean_object* v___x_170_; 
lean_inc(v_pos_160_);
lean_dec(v_expected_151_);
v___x_170_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_153_, v_a_152_, v_pos_160_);
lean_dec(v_pos_160_);
v___y_155_ = v___x_170_;
goto v___jp_154_;
}
}
else
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Parser_ParserState_mkEOIError(v_a_153_, v_expected_151_);
v___y_155_ = v___x_171_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v_errorMsg_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v_errorMsg_156_ = lean_ctor_get(v___y_155_, 4);
v___x_157_ = lean_box(0);
v___x_158_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_dec_ref(v_p_150_);
return v___y_155_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Parser_takeWhileFn(v_p_150_, v_a_152_, v___y_155_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object* v_p_172_, lean_object* v_expected_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lake_Toml_takeWhile1Fn(v_p_172_, v_expected_173_, v_a_174_, v_a_175_);
lean_dec_ref(v_a_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object* v_expected_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_pos_180_; lean_object* v_toInputContext_181_; uint8_t v___x_182_; 
v_pos_180_ = lean_ctor_get(v_a_179_, 2);
v_toInputContext_181_ = lean_ctor_get(v_a_178_, 0);
v___x_182_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_181_, v_pos_180_);
if (v___x_182_ == 0)
{
lean_object* v_inputString_183_; uint32_t v_curr_184_; uint32_t v___x_188_; uint8_t v___x_189_; 
v_inputString_183_ = lean_ctor_get(v_toInputContext_181_, 0);
v_curr_184_ = lean_string_utf8_get_fast(v_inputString_183_, v_pos_180_);
v___x_188_ = 48;
v___x_189_ = lean_uint32_dec_le(v___x_188_, v_curr_184_);
if (v___x_189_ == 0)
{
goto v___jp_185_;
}
else
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 57;
v___x_191_ = lean_uint32_dec_le(v_curr_184_, v___x_190_);
if (v___x_191_ == 0)
{
goto v___jp_185_;
}
else
{
lean_object* v___x_192_; 
lean_inc(v_pos_180_);
lean_dec(v_expected_177_);
v___x_192_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_179_, v_a_178_, v_pos_180_);
lean_dec(v_pos_180_);
return v___x_192_;
}
}
v___jp_185_:
{
uint8_t v___x_186_; lean_object* v___x_187_; 
v___x_186_ = 1;
v___x_187_ = l_Lake_Toml_mkUnexpectedCharError(v_a_179_, v_curr_184_, v_expected_177_, v___x_186_);
return v___x_187_;
}
}
else
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Parser_ParserState_mkEOIError(v_a_179_, v_expected_177_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object* v_expected_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lake_Toml_digitFn(v_expected_194_, v_a_195_, v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object* v_expected_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_s_201_; lean_object* v_errorMsg_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
lean_inc(v_expected_198_);
v_s_201_ = l_Lake_Toml_digitFn(v_expected_198_, v_a_199_, v_a_200_);
v_errorMsg_202_ = lean_ctor_get(v_s_201_, 4);
lean_inc(v_errorMsg_202_);
v___x_203_ = lean_box(0);
v___x_204_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_202_, v___x_203_);
lean_dec(v_errorMsg_202_);
if (v___x_204_ == 0)
{
lean_dec(v_expected_198_);
return v_s_201_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Lake_Toml_digitFn(v_expected_198_, v_a_199_, v_s_201_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object* v_expected_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lake_Toml_digitPairFn(v_expected_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t v_c_210_, lean_object* v_expected_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_pos_214_; lean_object* v_toInputContext_215_; uint8_t v___x_216_; 
v_pos_214_ = lean_ctor_get(v_a_213_, 2);
v_toInputContext_215_ = lean_ctor_get(v_a_212_, 0);
v___x_216_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_215_, v_pos_214_);
if (v___x_216_ == 0)
{
lean_object* v_inputString_217_; uint32_t v_curr_218_; uint8_t v___x_219_; 
v_inputString_217_ = lean_ctor_get(v_toInputContext_215_, 0);
v_curr_218_ = lean_string_utf8_get_fast(v_inputString_217_, v_pos_214_);
v___x_219_ = lean_uint32_dec_eq(v_curr_218_, v_c_210_);
if (v___x_219_ == 0)
{
uint8_t v___x_220_; lean_object* v___x_221_; 
v___x_220_ = 1;
v___x_221_ = l_Lake_Toml_mkUnexpectedCharError(v_a_213_, v_curr_218_, v_expected_211_, v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
lean_inc(v_pos_214_);
lean_dec(v_expected_211_);
v___x_222_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_213_, v_a_212_, v_pos_214_);
lean_dec(v_pos_214_);
return v___x_222_;
}
}
else
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Parser_ParserState_mkEOIError(v_a_213_, v_expected_211_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object* v_c_224_, lean_object* v_expected_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
uint32_t v_c_boxed_228_; lean_object* v_res_229_; 
v_c_boxed_228_ = lean_unbox_uint32(v_c_224_);
lean_dec(v_c_224_);
v_res_229_ = l_Lake_Toml_chFn(v_c_boxed_228_, v_expected_225_, v_a_226_, v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object* v_str_230_, lean_object* v_expected_231_, lean_object* v_strPos_232_, lean_object* v_c_233_, lean_object* v_s_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = lean_string_utf8_at_end(v_str_230_, v_strPos_232_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; lean_object* v_s_237_; lean_object* v_errorMsg_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_236_ = lean_string_utf8_get_fast(v_str_230_, v_strPos_232_);
lean_inc(v_expected_231_);
v_s_237_ = l_Lake_Toml_chFn(v___x_236_, v_expected_231_, v_c_233_, v_s_234_);
v_errorMsg_238_ = lean_ctor_get(v_s_237_, 4);
lean_inc(v_errorMsg_238_);
v___x_239_ = lean_box(0);
v___x_240_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_238_, v___x_239_);
lean_dec(v_errorMsg_238_);
if (v___x_240_ == 0)
{
lean_dec(v_strPos_232_);
lean_dec(v_expected_231_);
return v_s_237_;
}
else
{
if (v___x_235_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_string_utf8_next_fast(v_str_230_, v_strPos_232_);
lean_dec(v_strPos_232_);
v_strPos_232_ = v___x_241_;
v_s_234_ = v_s_237_;
goto _start;
}
else
{
lean_dec(v_strPos_232_);
lean_dec(v_expected_231_);
return v_s_237_;
}
}
}
else
{
lean_dec(v_strPos_232_);
lean_dec(v_expected_231_);
return v_s_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object* v_str_243_, lean_object* v_expected_244_, lean_object* v_strPos_245_, lean_object* v_c_246_, lean_object* v_s_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lake_Toml_strAuxFn(v_str_243_, v_expected_244_, v_strPos_245_, v_c_246_, v_s_247_);
lean_dec_ref(v_c_246_);
lean_dec_ref(v_str_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object* v_str_249_, lean_object* v_expected_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_alloc_closure((void*)(l_Lake_Toml_strAuxFn___boxed), 5, 3);
lean_closure_set(v___x_254_, 0, v_str_249_);
lean_closure_set(v___x_254_, 1, v_expected_250_);
lean_closure_set(v___x_254_, 2, v___x_253_);
v___x_255_ = l_Lean_Parser_atomicFn(v___x_254_, v_a_251_, v_a_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn(lean_object* v_p_257_, uint32_t v_sep_258_, lean_object* v_expected_259_, lean_object* v_c_260_, lean_object* v_s_261_){
_start:
{
lean_object* v_pos_262_; lean_object* v_toInputContext_263_; uint8_t v___x_264_; 
v_pos_262_ = lean_ctor_get(v_s_261_, 2);
v_toInputContext_263_ = lean_ctor_get(v_c_260_, 0);
v___x_264_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_263_, v_pos_262_);
if (v___x_264_ == 0)
{
lean_object* v_inputString_265_; uint32_t v_curr_266_; lean_object* v_s_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
lean_inc(v_pos_262_);
v_inputString_265_ = lean_ctor_get(v_toInputContext_263_, 0);
v_curr_266_ = lean_string_utf8_get_fast(v_inputString_265_, v_pos_262_);
v_s_267_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_261_, v_c_260_, v_pos_262_);
lean_dec(v_pos_262_);
v___x_268_ = lean_box_uint32(v_curr_266_);
lean_inc_ref(v_p_257_);
v___x_269_ = lean_apply_1(v_p_257_, v___x_268_);
v___x_270_ = lean_unbox(v___x_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; uint8_t v___x_272_; 
lean_dec_ref(v_p_257_);
v___x_271_ = 1;
v___x_272_ = lean_uint32_dec_eq(v_curr_266_, v_sep_258_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = l_Lake_Toml_mkUnexpectedCharError(v_s_267_, v_curr_266_, v_expected_259_, v___x_271_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_274_ = ((lean_object*)(l_Lake_Toml_sepByChar1Fn___closed__0));
v___x_275_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_276_ = lean_string_push(v___x_275_, v_curr_266_);
v___x_277_ = lean_string_append(v___x_274_, v___x_276_);
lean_dec_ref(v___x_276_);
v___x_278_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
v___x_280_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_267_, v___x_279_, v_expected_259_, v___x_271_);
return v___x_280_;
}
}
else
{
lean_object* v___x_281_; 
v___x_281_ = l_Lake_Toml_sepByChar1AuxFn(v_p_257_, v_sep_258_, v_expected_259_, v_c_260_, v_s_267_);
return v___x_281_;
}
}
else
{
lean_dec(v_expected_259_);
lean_dec_ref(v_p_257_);
return v_s_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object* v_p_282_, uint32_t v_sep_283_, lean_object* v_expected_284_, lean_object* v_c_285_, lean_object* v_s_286_){
_start:
{
lean_object* v_pos_287_; lean_object* v_toInputContext_288_; uint8_t v___x_289_; 
v_pos_287_ = lean_ctor_get(v_s_286_, 2);
v_toInputContext_288_ = lean_ctor_get(v_c_285_, 0);
v___x_289_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_288_, v_pos_287_);
if (v___x_289_ == 0)
{
lean_object* v_inputString_290_; uint32_t v_curr_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_inputString_290_ = lean_ctor_get(v_toInputContext_288_, 0);
v_curr_291_ = lean_string_utf8_get_fast(v_inputString_290_, v_pos_287_);
v___x_292_ = lean_box_uint32(v_curr_291_);
lean_inc_ref(v_p_282_);
v___x_293_ = lean_apply_1(v_p_282_, v___x_292_);
v___x_294_ = lean_unbox(v___x_293_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; 
v___x_295_ = lean_uint32_dec_eq(v_curr_291_, v_sep_283_);
if (v___x_295_ == 0)
{
lean_dec(v_expected_284_);
lean_dec_ref(v_p_282_);
return v_s_286_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_inc(v_pos_287_);
v___x_296_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_286_, v_c_285_, v_pos_287_);
lean_dec(v_pos_287_);
v___x_297_ = l_Lake_Toml_sepByChar1Fn(v_p_282_, v_sep_283_, v_expected_284_, v_c_285_, v___x_296_);
return v___x_297_;
}
}
else
{
lean_object* v___x_298_; 
lean_inc(v_pos_287_);
v___x_298_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_286_, v_c_285_, v_pos_287_);
lean_dec(v_pos_287_);
v_s_286_ = v___x_298_;
goto _start;
}
}
else
{
lean_dec(v_expected_284_);
lean_dec_ref(v_p_282_);
return v_s_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object* v_p_300_, lean_object* v_sep_301_, lean_object* v_expected_302_, lean_object* v_c_303_, lean_object* v_s_304_){
_start:
{
uint32_t v_sep_boxed_305_; lean_object* v_res_306_; 
v_sep_boxed_305_ = lean_unbox_uint32(v_sep_301_);
lean_dec(v_sep_301_);
v_res_306_ = l_Lake_Toml_sepByChar1AuxFn(v_p_300_, v_sep_boxed_305_, v_expected_302_, v_c_303_, v_s_304_);
lean_dec_ref(v_c_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object* v_p_307_, lean_object* v_sep_308_, lean_object* v_expected_309_, lean_object* v_c_310_, lean_object* v_s_311_){
_start:
{
uint32_t v_sep_boxed_312_; lean_object* v_res_313_; 
v_sep_boxed_312_ = lean_unbox_uint32(v_sep_308_);
lean_dec(v_sep_308_);
v_res_313_ = l_Lake_Toml_sepByChar1Fn(v_p_307_, v_sep_boxed_312_, v_expected_309_, v_c_310_, v_s_311_);
lean_dec_ref(v_c_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object* v_startPos_314_, lean_object* v_trailingFn_315_, lean_object* v_c_316_, lean_object* v_s_317_){
_start:
{
lean_object* v_toInputContext_318_; lean_object* v_pos_319_; lean_object* v_inputString_320_; lean_object* v_endPos_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_341_; 
v_toInputContext_318_ = lean_ctor_get(v_c_316_, 0);
lean_inc_ref(v_toInputContext_318_);
v_pos_319_ = lean_ctor_get(v_s_317_, 2);
lean_inc(v_pos_319_);
v_inputString_320_ = lean_ctor_get(v_toInputContext_318_, 0);
v_endPos_321_ = lean_ctor_get(v_toInputContext_318_, 3);
v_isSharedCheck_341_ = !lean_is_exclusive(v_toInputContext_318_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_342_ = lean_ctor_get(v_toInputContext_318_, 2);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_toInputContext_318_, 1);
lean_dec(v_unused_343_);
v___x_323_ = v_toInputContext_318_;
v_isShared_324_ = v_isSharedCheck_341_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_endPos_321_);
lean_inc(v_inputString_320_);
lean_dec(v_toInputContext_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_341_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_leading_325_; lean_object* v_s_326_; lean_object* v_pos_327_; lean_object* v_val_328_; lean_object* v___y_330_; uint8_t v___x_338_; 
lean_inc(v_startPos_314_);
v_leading_325_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_316_, v_startPos_314_);
v_s_326_ = lean_apply_2(v_trailingFn_315_, v_c_316_, v_s_317_);
v_pos_327_ = lean_ctor_get(v_s_326_, 2);
lean_inc(v_pos_327_);
v_val_328_ = lean_string_utf8_extract(v_inputString_320_, v_startPos_314_, v_pos_319_);
v___x_338_ = lean_nat_dec_le(v_pos_327_, v_endPos_321_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec(v_pos_327_);
v___x_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_339_, 0, v_inputString_320_);
lean_ctor_set(v___x_339_, 1, v_pos_319_);
lean_ctor_set(v___x_339_, 2, v_endPos_321_);
v___y_330_ = v___x_339_;
goto v___jp_329_;
}
else
{
lean_object* v___x_340_; 
lean_dec(v_endPos_321_);
v___x_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_340_, 0, v_inputString_320_);
lean_ctor_set(v___x_340_, 1, v_pos_319_);
lean_ctor_set(v___x_340_, 2, v_pos_327_);
v___y_330_ = v___x_340_;
goto v___jp_329_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = lean_string_utf8_byte_size(v_val_328_);
v___x_332_ = lean_nat_add(v_startPos_314_, v___x_331_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 3, v___x_332_);
lean_ctor_set(v___x_323_, 2, v___y_330_);
lean_ctor_set(v___x_323_, 1, v_startPos_314_);
lean_ctor_set(v___x_323_, 0, v_leading_325_);
v___x_334_ = v___x_323_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_leading_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_startPos_314_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v___y_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v___x_332_);
v___x_334_ = v_reuseFailAlloc_337_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v_atom_335_; lean_object* v___x_336_; 
v_atom_335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_335_, 0, v___x_334_);
lean_ctor_set(v_atom_335_, 1, v_val_328_);
v___x_336_ = l_Lean_Parser_ParserState_pushSyntax(v_s_326_, v_atom_335_);
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object* v_p_344_, lean_object* v_trailingFn_345_, lean_object* v_c_346_, lean_object* v_s_347_){
_start:
{
lean_object* v_pos_348_; lean_object* v_s_349_; lean_object* v_errorMsg_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_pos_348_ = lean_ctor_get(v_s_347_, 2);
lean_inc(v_pos_348_);
lean_inc_ref(v_c_346_);
v_s_349_ = lean_apply_2(v_p_344_, v_c_346_, v_s_347_);
v_errorMsg_350_ = lean_ctor_get(v_s_349_, 4);
lean_inc(v_errorMsg_350_);
v___x_351_ = lean_box(0);
v___x_352_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_350_, v___x_351_);
lean_dec(v_errorMsg_350_);
if (v___x_352_ == 0)
{
lean_dec(v_pos_348_);
lean_dec_ref(v_c_346_);
lean_dec_ref(v_trailingFn_345_);
return v_s_349_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = l_Lake_Toml_pushAtom(v_pos_348_, v_trailingFn_345_, v_c_346_, v_s_349_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object* v___y_354_){
_start:
{
lean_inc(v___y_354_);
return v___y_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lake_Toml_atom___lam__0(v___y_355_);
lean_dec(v___y_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object* v___y_357_){
_start:
{
lean_inc_ref(v___y_357_);
return v___y_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lake_Toml_atom___lam__1(v___y_358_);
lean_dec_ref(v___y_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object* v_p_366_, lean_object* v_trailingFn_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_369_ = lean_alloc_closure((void*)(l_Lake_Toml_atomFn), 4, 2);
lean_closure_set(v___x_369_, 0, v_p_366_);
lean_closure_set(v___x_369_, 1, v_trailingFn_367_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v_stxTrav_374_; lean_object* v_cur_375_; lean_object* v___x_376_; 
v___x_373_ = lean_st_ref_get(v___y_371_);
v_stxTrav_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc_ref(v_stxTrav_374_);
lean_dec(v___x_373_);
v_cur_375_ = lean_ctor_get(v_stxTrav_374_, 0);
lean_inc(v_cur_375_);
lean_dec_ref(v_stxTrav_374_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_cur_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_377_);
lean_dec(v___y_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_381_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_stxTrav_395_; lean_object* v_leadWord_396_; uint8_t v_leadWordIdent_397_; uint8_t v_isUngrouped_398_; uint8_t v_mustBeGrouped_399_; lean_object* v_stack_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v___x_394_ = lean_st_ref_take(v___y_392_);
v_stxTrav_395_ = lean_ctor_get(v___x_394_, 0);
v_leadWord_396_ = lean_ctor_get(v___x_394_, 1);
v_leadWordIdent_397_ = lean_ctor_get_uint8(v___x_394_, sizeof(void*)*3);
v_isUngrouped_398_ = lean_ctor_get_uint8(v___x_394_, sizeof(void*)*3 + 1);
v_mustBeGrouped_399_ = lean_ctor_get_uint8(v___x_394_, sizeof(void*)*3 + 2);
v_stack_400_ = lean_ctor_get(v___x_394_, 2);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v___x_394_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_stack_400_);
lean_inc(v_leadWord_396_);
lean_inc(v_stxTrav_395_);
lean_dec(v___x_394_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_Syntax_Traverser_left(v_stxTrav_395_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_leadWord_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_stack_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*3, v_leadWordIdent_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*3 + 1, v_isUngrouped_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*3 + 2, v_mustBeGrouped_399_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_st_ref_put(v___y_392_, v___x_406_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_412_);
lean_dec(v___y_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_416_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_427_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_ctor_set(v___x_432_, 4, v___x_430_);
lean_ctor_set(v___x_432_, 5, v___x_430_);
lean_ctor_set(v___x_432_, 6, v___x_430_);
lean_ctor_set(v___x_432_, 7, v___x_430_);
lean_ctor_set(v___x_432_, 8, v___x_430_);
lean_ctor_set(v___x_432_, 9, v___x_430_);
lean_ctor_set(v___x_432_, 10, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(32u);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_436_ = ((size_t)5ULL);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_unsigned_to_nat(32u);
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
v___x_440_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3);
v___x_441_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_437_);
lean_ctor_set(v___x_441_, 3, v___x_437_);
lean_ctor_set_usize(v___x_441_, 4, v___x_436_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_442_ = lean_box(1);
v___x_443_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4);
v___x_444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(lean_object* v_msgData_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; lean_object* v_env_451_; lean_object* v_options_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_450_ = lean_st_ref_get(v___y_448_);
v_env_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_451_);
lean_dec(v___x_450_);
v_options_452_ = lean_ctor_get(v___y_447_, 1);
v___x_453_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_452_);
v___x_455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_455_, 0, v_env_451_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
lean_ctor_set(v___x_455_, 3, v_options_452_);
v___x_456_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_msgData_446_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(lean_object* v_msgData_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_462_;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_463_; double v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_float_of_nat(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* v_cls_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_ref_472_; lean_object* v___x_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_518_; 
v_ref_472_ = lean_ctor_get(v___y_469_, 4);
v___x_473_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_468_, v___y_469_, v___y_470_);
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_518_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_518_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_518_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v_traceState_479_; lean_object* v_env_480_; lean_object* v_nextMacroScope_481_; lean_object* v_ngen_482_; lean_object* v_auxDeclNGen_483_; lean_object* v_cache_484_; lean_object* v_messages_485_; lean_object* v_infoState_486_; lean_object* v_snapshotTasks_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_517_; 
v___x_478_ = lean_st_ref_take(v___y_470_);
v_traceState_479_ = lean_ctor_get(v___x_478_, 4);
v_env_480_ = lean_ctor_get(v___x_478_, 0);
v_nextMacroScope_481_ = lean_ctor_get(v___x_478_, 1);
v_ngen_482_ = lean_ctor_get(v___x_478_, 2);
v_auxDeclNGen_483_ = lean_ctor_get(v___x_478_, 3);
v_cache_484_ = lean_ctor_get(v___x_478_, 5);
v_messages_485_ = lean_ctor_get(v___x_478_, 6);
v_infoState_486_ = lean_ctor_get(v___x_478_, 7);
v_snapshotTasks_487_ = lean_ctor_get(v___x_478_, 8);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_517_ == 0)
{
v___x_489_ = v___x_478_;
v_isShared_490_ = v_isSharedCheck_517_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_snapshotTasks_487_);
lean_inc(v_infoState_486_);
lean_inc(v_messages_485_);
lean_inc(v_cache_484_);
lean_inc(v_traceState_479_);
lean_inc(v_auxDeclNGen_483_);
lean_inc(v_ngen_482_);
lean_inc(v_nextMacroScope_481_);
lean_inc(v_env_480_);
lean_dec(v___x_478_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_517_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint64_t v_tid_491_; lean_object* v_traces_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_516_; 
v_tid_491_ = lean_ctor_get_uint64(v_traceState_479_, sizeof(void*)*1);
v_traces_492_ = lean_ctor_get(v_traceState_479_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_traceState_479_);
if (v_isSharedCheck_516_ == 0)
{
v___x_494_ = v_traceState_479_;
v_isShared_495_ = v_isSharedCheck_516_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_traces_492_);
lean_dec(v_traceState_479_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_516_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; double v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_496_ = lean_box(0);
v___x_497_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_498_ = 0;
v___x_499_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_500_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_500_, 0, v_cls_467_);
lean_ctor_set(v___x_500_, 1, v___x_496_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_ctor_set_float(v___x_500_, sizeof(void*)*3, v___x_497_);
lean_ctor_set_float(v___x_500_, sizeof(void*)*3 + 8, v___x_497_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*3 + 16, v___x_498_);
v___x_501_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_502_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v_a_474_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
lean_inc(v_ref_472_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_472_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_PersistentArray_push___redArg(v_traces_492_, v___x_503_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_504_);
v___x_506_ = v___x_494_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_504_);
lean_ctor_set_uint64(v_reuseFailAlloc_515_, sizeof(void*)*1, v_tid_491_);
v___x_506_ = v_reuseFailAlloc_515_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 4, v___x_506_);
v___x_508_ = v___x_489_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_env_480_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_nextMacroScope_481_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_ngen_482_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_auxDeclNGen_483_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_cache_484_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_messages_485_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_infoState_486_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v_snapshotTasks_487_);
v___x_508_ = v_reuseFailAlloc_514_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_509_ = lean_st_ref_put(v___y_470_, v___x_508_);
v___x_510_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_510_);
v___x_512_ = v___x_476_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_519_, lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_519_, v_msg_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_524_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_536_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__5));
v___x_537_ = l_Lean_Name_append(v___x_536_, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__8(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__7));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__10(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__9));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_549_; lean_object* v_a_550_; 
v___x_549_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_545_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_549_);
if (lean_obj_tag(v_a_550_) == 2)
{
lean_object* v_info_551_; lean_object* v_val_552_; lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_info_551_ = lean_ctor_get(v_a_550_, 0);
lean_inc(v_info_551_);
v_val_552_ = lean_ctor_get(v_a_550_, 1);
lean_inc_ref(v_val_552_);
v___x_553_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_550_);
lean_dec_ref_known(v_a_550_, 2);
v___x_554_ = 0;
v___x_555_ = lean_box(v___x_554_);
v___x_556_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_556_, 0, v_info_551_);
lean_closure_set(v___x_556_, 1, v_val_552_);
lean_closure_set(v___x_556_, 2, v___x_555_);
v___x_557_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_553_, v___x_556_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v___x_553_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
lean_dec_ref_known(v___x_557_, 1);
v___x_558_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_545_);
return v___x_558_;
}
else
{
return v___x_557_;
}
}
else
{
lean_object* v_options_559_; uint8_t v_hasTrace_560_; 
v_options_559_ = lean_ctor_get(v_a_546_, 1);
v_hasTrace_560_ = lean_ctor_get_uint8(v_options_559_, sizeof(void*)*1);
if (v_hasTrace_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec(v_a_550_);
v___x_561_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_561_;
}
else
{
lean_object* v_toCold_562_; lean_object* v_inheritedTraceOptions_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_toCold_562_ = lean_ctor_get(v_a_546_, 0);
v_inheritedTraceOptions_563_ = lean_ctor_get(v_toCold_562_, 4);
v___x_564_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_565_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_563_, v_options_559_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
lean_dec(v_a_550_);
v___x_567_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_567_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_568_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_569_ = lean_box(0);
v___x_570_ = 0;
v___x_571_ = l_Lean_Syntax_formatStx(v_a_550_, v___x_569_, v___x_570_);
v___x_572_ = l_Lean_MessageData_ofFormat(v___x_571_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_568_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_564_, v___x_575_, v_a_546_, v_a_547_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; 
lean_dec_ref_known(v___x_576_, 1);
v___x_577_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_577_;
}
else
{
return v___x_576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lake_Toml_atom_formatter___redArg(v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lake_Toml_atom_formatter___redArg(v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lake_Toml_atom_formatter(v_x_592_, v_x_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec_ref(v_x_593_);
lean_dec_ref(v_x_592_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_600_, lean_object* v_msg_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_600_, v_msg_601_, v___y_604_, v___y_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_608_, v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_619_);
lean_dec(v_a_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_625_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_630_, v_x_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec_ref(v_x_631_);
lean_dec_ref(v_x_630_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_638_, lean_object* v_expected_639_, lean_object* v_trailingFn_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_box_uint32(v_c_638_);
v___x_642_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_642_, 0, v___x_641_);
lean_closure_set(v___x_642_, 1, v_expected_639_);
v___x_643_ = l_Lake_Toml_atom(v___x_642_, v_trailingFn_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_644_, lean_object* v_expected_645_, lean_object* v_trailingFn_646_){
_start:
{
uint32_t v_c_boxed_647_; lean_object* v_res_648_; 
v_c_boxed_647_ = lean_unbox_uint32(v_c_644_);
lean_dec(v_c_644_);
v_res_648_ = l_Lake_Toml_chAtom(v_c_boxed_647_, v_expected_645_, v_trailingFn_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
uint8_t v___x_655_; lean_object* v___x_656_; 
v___x_655_ = 0;
v___x_656_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_649_, v___x_655_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
uint32_t v_c_boxed_663_; lean_object* v_res_664_; 
v_c_boxed_663_ = lean_unbox_uint32(v_c_657_);
lean_dec(v_c_657_);
v_res_664_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_663_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_665_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_674_, lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
uint32_t v_c_boxed_682_; lean_object* v_res_683_; 
v_c_boxed_682_ = lean_unbox_uint32(v_c_674_);
lean_dec(v_c_674_);
v_res_683_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_682_, v_x_675_, v_x_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec_ref(v_x_676_);
lean_dec(v_x_675_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_687_);
lean_dec(v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
uint32_t v_x_18__boxed_707_; lean_object* v_res_708_; 
v_x_18__boxed_707_ = lean_unbox_uint32(v_x_699_);
lean_dec(v_x_699_);
v_res_708_ = l_Lake_Toml_chAtom_parenthesizer(v_x_18__boxed_707_, v_x_700_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec_ref(v_x_701_);
lean_dec(v_x_700_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_709_, lean_object* v_expected_710_, lean_object* v_trailingFn_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_str_716_; lean_object* v_startInclusive_717_; lean_object* v_endExclusive_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_string_utf8_byte_size(v_s_709_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_s_709_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
v___x_715_ = l_String_Slice_trimAscii(v___x_714_);
v_str_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc_ref(v_str_716_);
v_startInclusive_717_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_startInclusive_717_);
v_endExclusive_718_ = lean_ctor_get(v___x_715_, 2);
lean_inc(v_endExclusive_718_);
lean_dec_ref(v___x_715_);
v___x_719_ = lean_string_utf8_extract_fast(v_str_716_, v_startInclusive_717_, v_endExclusive_718_);
lean_dec(v_endExclusive_718_);
lean_dec(v_startInclusive_717_);
lean_dec_ref(v_str_716_);
v___x_720_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_720_, 0, v___x_719_);
lean_closure_set(v___x_720_, 1, v_expected_710_);
v___x_721_ = l_Lake_Toml_atom(v___x_720_, v_trailingFn_711_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_736_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lake_Toml_strAtom_formatter(v_s_745_, v_x_746_, v_x_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec_ref(v_x_747_);
lean_dec(v_x_746_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_757_);
lean_dec(v_a_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lake_Toml_strAtom_parenthesizer(v_x_769_, v_x_770_, v_x_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v_x_771_);
lean_dec(v_x_770_);
lean_dec_ref(v_x_769_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_778_, lean_object* v_startPos_779_, lean_object* v_trailingFn_780_, lean_object* v_c_781_, lean_object* v_s_782_){
_start:
{
lean_object* v_toInputContext_783_; lean_object* v_pos_784_; lean_object* v_inputString_785_; lean_object* v_endPos_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_804_; 
v_toInputContext_783_ = lean_ctor_get(v_c_781_, 0);
lean_inc_ref(v_toInputContext_783_);
v_pos_784_ = lean_ctor_get(v_s_782_, 2);
lean_inc(v_pos_784_);
v_inputString_785_ = lean_ctor_get(v_toInputContext_783_, 0);
v_endPos_786_ = lean_ctor_get(v_toInputContext_783_, 3);
v_isSharedCheck_804_ = !lean_is_exclusive(v_toInputContext_783_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; lean_object* v_unused_806_; 
v_unused_805_ = lean_ctor_get(v_toInputContext_783_, 2);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_toInputContext_783_, 1);
lean_dec(v_unused_806_);
v___x_788_ = v_toInputContext_783_;
v_isShared_789_ = v_isSharedCheck_804_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_endPos_786_);
lean_inc(v_inputString_785_);
lean_dec(v_toInputContext_783_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_804_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_leading_790_; lean_object* v_s_791_; lean_object* v_pos_792_; lean_object* v_val_793_; lean_object* v___y_795_; uint8_t v___x_801_; 
lean_inc(v_startPos_779_);
v_leading_790_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_781_, v_startPos_779_);
v_s_791_ = lean_apply_2(v_trailingFn_780_, v_c_781_, v_s_782_);
v_pos_792_ = lean_ctor_get(v_s_791_, 2);
lean_inc(v_pos_792_);
v_val_793_ = lean_string_utf8_extract(v_inputString_785_, v_startPos_779_, v_pos_784_);
v___x_801_ = lean_nat_dec_le(v_pos_792_, v_endPos_786_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v_pos_792_);
lean_inc(v_pos_784_);
v___x_802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_802_, 0, v_inputString_785_);
lean_ctor_set(v___x_802_, 1, v_pos_784_);
lean_ctor_set(v___x_802_, 2, v_endPos_786_);
v___y_795_ = v___x_802_;
goto v___jp_794_;
}
else
{
lean_object* v___x_803_; 
lean_dec(v_endPos_786_);
lean_inc(v_pos_784_);
v___x_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_803_, 0, v_inputString_785_);
lean_ctor_set(v___x_803_, 1, v_pos_784_);
lean_ctor_set(v___x_803_, 2, v_pos_792_);
v___y_795_ = v___x_803_;
goto v___jp_794_;
}
v___jp_794_:
{
lean_object* v_info_797_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 3, v_pos_784_);
lean_ctor_set(v___x_788_, 2, v___y_795_);
lean_ctor_set(v___x_788_, 1, v_startPos_779_);
lean_ctor_set(v___x_788_, 0, v_leading_790_);
v_info_797_ = v___x_788_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_leading_790_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_startPos_779_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v___y_795_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_pos_784_);
v_info_797_ = v_reuseFailAlloc_800_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = l_Lean_Syntax_mkLit(v_kind_778_, v_val_793_, v_info_797_);
v___x_799_ = l_Lean_Parser_ParserState_pushSyntax(v_s_791_, v___x_798_);
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_807_, lean_object* v_p_808_, lean_object* v_trailingFn_809_, lean_object* v_c_810_, lean_object* v_s_811_){
_start:
{
lean_object* v_pos_812_; lean_object* v_s_813_; lean_object* v_errorMsg_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_pos_812_ = lean_ctor_get(v_s_811_, 2);
lean_inc(v_pos_812_);
lean_inc_ref(v_c_810_);
v_s_813_ = lean_apply_2(v_p_808_, v_c_810_, v_s_811_);
v_errorMsg_814_ = lean_ctor_get(v_s_813_, 4);
lean_inc(v_errorMsg_814_);
v___x_815_ = lean_box(0);
v___x_816_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_814_, v___x_815_);
lean_dec(v_errorMsg_814_);
if (v___x_816_ == 0)
{
lean_dec(v_pos_812_);
lean_dec_ref(v_c_810_);
lean_dec_ref(v_trailingFn_809_);
lean_dec(v_kind_807_);
return v_s_813_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = l_Lake_Toml_pushLit(v_kind_807_, v_pos_812_, v_trailingFn_809_, v_c_810_, v_s_813_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_818_, lean_object* v_p_819_, lean_object* v_trailingFn_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_822_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_822_, 0, v_kind_818_);
lean_closure_set(v___x_822_, 1, v_p_819_);
lean_closure_set(v___x_822_, 2, v_trailingFn_820_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lake_Toml_lit_formatter___redArg(v_kind_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_838_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lake_Toml_lit_formatter(v_kind_847_, v_x_848_, v_x_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec_ref(v_x_849_);
lean_dec_ref(v_x_848_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_859_);
lean_dec(v_a_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_866_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lake_Toml_lit_parenthesizer(v_x_871_, v_x_872_, v_x_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec_ref(v_x_873_);
lean_dec_ref(v_x_872_);
lean_dec(v_x_871_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_894_, lean_object* v_kind_895_, uint8_t v_anonymous_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___f_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_inc(v_kind_895_);
v___f_902_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_902_, 0, v_kind_895_);
v___x_903_ = 0;
v___x_904_ = lean_box(v_anonymous_896_);
v___x_905_ = lean_box(v___x_903_);
v___x_906_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_906_, 0, v_name_894_);
lean_closure_set(v___x_906_, 1, v_kind_895_);
lean_closure_set(v___x_906_, 2, v___x_904_);
lean_closure_set(v___x_906_, 3, v___x_905_);
v___x_907_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_906_, v___f_902_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_908_, lean_object* v_kind_909_, lean_object* v_anonymous_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
uint8_t v_anonymous_boxed_916_; lean_object* v_res_917_; 
v_anonymous_boxed_916_ = lean_unbox(v_anonymous_910_);
v_res_917_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_908_, v_kind_909_, v_anonymous_boxed_916_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_918_, lean_object* v_kind_919_, lean_object* v_p_920_, lean_object* v_trailingFn_921_, uint8_t v_anonymous_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_918_, v_kind_919_, v_anonymous_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_929_, lean_object* v_kind_930_, lean_object* v_p_931_, lean_object* v_trailingFn_932_, lean_object* v_anonymous_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
uint8_t v_anonymous_boxed_939_; lean_object* v_res_940_; 
v_anonymous_boxed_939_ = lean_unbox(v_anonymous_933_);
v_res_940_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_929_, v_kind_930_, v_p_931_, v_trailingFn_932_, v_anonymous_boxed_939_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec_ref(v_trailingFn_932_);
lean_dec_ref(v_p_931_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_954_, lean_object* v_kind_955_, uint8_t v_anonymous_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___f_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___f_962_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_963_ = 0;
v___x_964_ = lean_box(v_anonymous_956_);
v___x_965_ = lean_box(v___x_963_);
v___x_966_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_966_, 0, v_name_954_);
lean_closure_set(v___x_966_, 1, v_kind_955_);
lean_closure_set(v___x_966_, 2, v___x_964_);
lean_closure_set(v___x_966_, 3, v___x_965_);
v___x_967_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_966_, v___f_962_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_968_, lean_object* v_kind_969_, lean_object* v_anonymous_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
uint8_t v_anonymous_boxed_976_; lean_object* v_res_977_; 
v_anonymous_boxed_976_ = lean_unbox(v_anonymous_970_);
v_res_977_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_968_, v_kind_969_, v_anonymous_boxed_976_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_978_, lean_object* v_kind_979_, lean_object* v_p_980_, lean_object* v_trailingFn_981_, uint8_t v_anonymous_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_978_, v_kind_979_, v_anonymous_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_989_, lean_object* v_kind_990_, lean_object* v_p_991_, lean_object* v_trailingFn_992_, lean_object* v_anonymous_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
uint8_t v_anonymous_boxed_999_; lean_object* v_res_1000_; 
v_anonymous_boxed_999_ = lean_unbox(v_anonymous_993_);
v_res_1000_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_989_, v_kind_990_, v_p_991_, v_trailingFn_992_, v_anonymous_boxed_999_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec_ref(v_trailingFn_992_);
lean_dec_ref(v_p_991_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1001_, lean_object* v_kind_1002_, lean_object* v_p_1003_, lean_object* v_trailingFn_1004_, uint8_t v_anonymous_1005_){
_start:
{
uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = 0;
lean_inc(v_kind_1002_);
v___x_1007_ = l_Lean_Parser_mkAntiquot(v_name_1001_, v_kind_1002_, v_anonymous_1005_, v___x_1006_);
v___x_1008_ = l_Lake_Toml_lit(v_kind_1002_, v_p_1003_, v_trailingFn_1004_);
v___x_1009_ = l_Lean_Parser_withAntiquot(v___x_1007_, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1010_, lean_object* v_kind_1011_, lean_object* v_p_1012_, lean_object* v_trailingFn_1013_, lean_object* v_anonymous_1014_){
_start:
{
uint8_t v_anonymous_boxed_1015_; lean_object* v_res_1016_; 
v_anonymous_boxed_1015_ = lean_unbox(v_anonymous_1014_);
v_res_1016_ = l_Lake_Toml_litWithAntiquot(v_name_1010_, v_kind_1011_, v_p_1012_, v_trailingFn_1013_, v_anonymous_boxed_1015_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_Lean_Parser_epsilonInfo;
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_fn_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lake_Toml_epsilon_formatter(v_x_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec_ref(v_x_1032_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_x_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1058_, lean_object* v_x_1059_){
_start:
{
switch(lean_obj_tag(v_x_1059_))
{
case 2:
{
lean_object* v_info_1060_; lean_object* v_val_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_info_1060_ = lean_ctor_get(v_x_1059_, 0);
v_val_1061_ = lean_ctor_get(v_x_1059_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_x_1059_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_val_1061_);
lean_inc(v_info_1060_);
lean_dec(v_x_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_apply_1(v_f_1058_, v_info_1060_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_val_1061_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
case 3:
{
lean_object* v_info_1070_; lean_object* v_rawVal_1071_; lean_object* v_val_1072_; lean_object* v_preresolved_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_info_1070_ = lean_ctor_get(v_x_1059_, 0);
v_rawVal_1071_ = lean_ctor_get(v_x_1059_, 1);
v_val_1072_ = lean_ctor_get(v_x_1059_, 2);
v_preresolved_1073_ = lean_ctor_get(v_x_1059_, 3);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v_x_1059_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_preresolved_1073_);
lean_inc(v_val_1072_);
lean_inc(v_rawVal_1071_);
lean_inc(v_info_1070_);
lean_dec(v_x_1059_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_apply_1(v_f_1058_, v_info_1070_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_rawVal_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_val_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_preresolved_1073_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
case 1:
{
lean_object* v_info_1082_; lean_object* v_kind_1083_; lean_object* v_args_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_info_1082_ = lean_ctor_get(v_x_1059_, 0);
v_kind_1083_ = lean_ctor_get(v_x_1059_, 1);
v_args_1084_ = lean_ctor_get(v_x_1059_, 2);
v___x_1085_ = lean_array_get_size(v_args_1084_);
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_sub(v___x_1085_, v___x_1086_);
v___x_1088_ = lean_nat_dec_lt(v___x_1087_, v___x_1085_);
if (v___x_1088_ == 0)
{
lean_dec(v___x_1087_);
lean_dec_ref(v_f_1058_);
return v_x_1059_;
}
else
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1100_; 
lean_inc_ref(v_args_1084_);
lean_inc(v_kind_1083_);
lean_inc(v_info_1082_);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; 
v_unused_1101_ = lean_ctor_get(v_x_1059_, 2);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_x_1059_, 1);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_x_1059_, 0);
lean_dec(v_unused_1103_);
v___x_1090_ = v_x_1059_;
v_isShared_1091_ = v_isSharedCheck_1100_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_x_1059_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1100_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_v_1092_; lean_object* v___x_1093_; lean_object* v_xs_x27_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v_v_1092_ = lean_array_fget(v_args_1084_, v___x_1087_);
v___x_1093_ = lean_box(0);
v_xs_x27_1094_ = lean_array_fset(v_args_1084_, v___x_1087_, v___x_1093_);
v___x_1095_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1058_, v_v_1092_);
v___x_1096_ = lean_array_fset(v_xs_x27_1094_, v___x_1087_, v___x_1095_);
lean_dec(v___x_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 2, v___x_1096_);
v___x_1098_ = v___x_1090_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_info_1082_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_kind_1083_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1058_);
return v_x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
lean_object* v_trailing_1106_; lean_object* v_leading_1107_; lean_object* v_pos_1108_; lean_object* v_endPos_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1126_; 
v_trailing_1106_ = lean_ctor_get(v_x_1105_, 2);
v_leading_1107_ = lean_ctor_get(v_x_1105_, 0);
v_pos_1108_ = lean_ctor_get(v_x_1105_, 1);
v_endPos_1109_ = lean_ctor_get(v_x_1105_, 3);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1111_ = v_x_1105_;
v_isShared_1112_ = v_isSharedCheck_1126_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_endPos_1109_);
lean_inc(v_trailing_1106_);
lean_inc(v_pos_1108_);
lean_inc(v_leading_1107_);
lean_dec(v_x_1105_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1126_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_str_1113_; lean_object* v_startPos_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1124_; 
v_str_1113_ = lean_ctor_get(v_trailing_1106_, 0);
v_startPos_1114_ = lean_ctor_get(v_trailing_1106_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_trailing_1106_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_trailing_1106_, 2);
lean_dec(v_unused_1125_);
v___x_1116_ = v_trailing_1106_;
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_startPos_1114_);
lean_inc(v_str_1113_);
lean_dec(v_trailing_1106_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 2, v_stopPos_1104_);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_str_1113_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_startPos_1114_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_stopPos_1104_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 2, v___x_1119_);
v___x_1121_ = v___x_1111_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_leading_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_pos_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_endPos_1109_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_dec(v_stopPos_1104_);
return v_x_1105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1127_, lean_object* v_x_1128_){
_start:
{
switch(lean_obj_tag(v_x_1128_))
{
case 2:
{
lean_object* v_info_1129_; lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_info_1129_ = lean_ctor_get(v_x_1128_, 0);
v_val_1130_ = lean_ctor_get(v_x_1128_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_x_1128_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_inc(v_info_1129_);
lean_dec(v_x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1127_, v_info_1129_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_val_1130_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
case 3:
{
lean_object* v_info_1139_; lean_object* v_rawVal_1140_; lean_object* v_val_1141_; lean_object* v_preresolved_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_info_1139_ = lean_ctor_get(v_x_1128_, 0);
v_rawVal_1140_ = lean_ctor_get(v_x_1128_, 1);
v_val_1141_ = lean_ctor_get(v_x_1128_, 2);
v_preresolved_1142_ = lean_ctor_get(v_x_1128_, 3);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v_x_1128_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_preresolved_1142_);
lean_inc(v_val_1141_);
lean_inc(v_rawVal_1140_);
lean_inc(v_info_1139_);
lean_dec(v_x_1128_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1127_, v_info_1139_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_rawVal_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_val_1141_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_preresolved_1142_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
case 1:
{
lean_object* v_info_1151_; lean_object* v_kind_1152_; lean_object* v_args_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_info_1151_ = lean_ctor_get(v_x_1128_, 0);
v_kind_1152_ = lean_ctor_get(v_x_1128_, 1);
v_args_1153_ = lean_ctor_get(v_x_1128_, 2);
v___x_1154_ = lean_array_get_size(v_args_1153_);
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_sub(v___x_1154_, v___x_1155_);
v___x_1157_ = lean_nat_dec_lt(v___x_1156_, v___x_1154_);
if (v___x_1157_ == 0)
{
lean_dec(v___x_1156_);
lean_dec(v_stopPos_1127_);
return v_x_1128_;
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1169_; 
lean_inc_ref(v_args_1153_);
lean_inc(v_kind_1152_);
lean_inc(v_info_1151_);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1128_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1170_ = lean_ctor_get(v_x_1128_, 2);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_x_1128_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_x_1128_, 0);
lean_dec(v_unused_1172_);
v___x_1159_ = v_x_1128_;
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_x_1128_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_v_1161_; lean_object* v___x_1162_; lean_object* v_xs_x27_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v_v_1161_ = lean_array_fget(v_args_1153_, v___x_1156_);
v___x_1162_ = lean_box(0);
v_xs_x27_1163_ = lean_array_fset(v_args_1153_, v___x_1156_, v___x_1162_);
v___x_1164_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1127_, v_v_1161_);
v___x_1165_ = lean_array_fset(v_xs_x27_1163_, v___x_1156_, v___x_1164_);
lean_dec(v___x_1156_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 2, v___x_1165_);
v___x_1167_ = v___x_1159_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_info_1151_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_kind_1152_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1127_);
return v_x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1173_, lean_object* v_c_1174_, lean_object* v_s_1175_){
_start:
{
lean_object* v_s_1176_; lean_object* v_stxStack_1177_; lean_object* v_pos_1178_; lean_object* v_tail_1179_; lean_object* v_s_1180_; lean_object* v_tail_1181_; lean_object* v___x_1182_; 
v_s_1176_ = lean_apply_2(v_p_1173_, v_c_1174_, v_s_1175_);
v_stxStack_1177_ = lean_ctor_get(v_s_1176_, 0);
lean_inc_ref(v_stxStack_1177_);
v_pos_1178_ = lean_ctor_get(v_s_1176_, 2);
lean_inc(v_pos_1178_);
v_tail_1179_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1177_);
lean_dec_ref(v_stxStack_1177_);
v_s_1180_ = l_Lean_Parser_ParserState_popSyntax(v_s_1176_);
v_tail_1181_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1178_, v_tail_1179_);
v___x_1182_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1180_, v_tail_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lake_Toml_trailing_formatter(v_p_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec_ref(v_p_1194_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lake_Toml_trailing_parenthesizer(v_p_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v_p_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1220_, 0, v_p_1219_);
v___x_1221_ = l_Lean_Parser_epsilonInfo;
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_p_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v_a_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1227_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = l_Lean_Syntax_getKind(v_a_1232_);
v___x_1234_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1233_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lake_Toml_dynamicNode_formatter(v_x_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec_ref(v_x_1248_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_stxTrav_1258_; lean_object* v_cur_1259_; lean_object* v___x_1260_; 
v___x_1257_ = lean_st_ref_get(v___y_1255_);
v_stxTrav_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_stxTrav_1258_);
lean_dec(v___x_1257_);
v_cur_1259_ = lean_ctor_get(v_stxTrav_1258_, 0);
lean_inc(v_cur_1259_);
lean_dec_ref(v_stxTrav_1258_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_cur_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1261_);
lean_dec(v___y_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1277_);
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = l_Lean_Syntax_getKind(v_a_1282_);
v___x_1284_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1283_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_x_1298_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_fn_1311_; lean_object* v___x_1312_; 
lean_inc_ref(v_f_1305_);
v___x_1308_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1308_, 0, v_f_1305_);
v___x_1309_ = l_Lake_Toml_dynamicNode(v___x_1308_);
v___x_1310_ = lean_apply_1(v_f_1305_, v___x_1309_);
v_fn_1311_ = lean_ctor_get(v___x_1310_, 1);
lean_inc_ref(v_fn_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = lean_apply_2(v_fn_1311_, v_a_1306_, v_a_1307_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lake_Toml_recNode_formatter(v_f_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec_ref(v_f_1332_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lake_Toml_recNode_parenthesizer(v_f_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec_ref(v_f_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1366_, 0, v_f_1365_);
v___x_1367_ = l_Lake_Toml_dynamicNode(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1368_, lean_object* v_kind_1369_, lean_object* v_f_1370_, uint8_t v_anonymous_1371_, lean_object* v_p_1372_){
_start:
{
uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1373_ = 1;
lean_inc(v_kind_1369_);
v___x_1374_ = l_Lean_Parser_mkAntiquot(v_name_1368_, v_kind_1369_, v_anonymous_1371_, v___x_1373_);
v___x_1375_ = lean_apply_1(v_f_1370_, v_p_1372_);
v___x_1376_ = l_Lean_Parser_withAntiquot(v___x_1374_, v___x_1375_);
v___x_1377_ = l_Lean_Parser_withCache(v_kind_1369_, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1378_, lean_object* v_kind_1379_, lean_object* v_f_1380_, lean_object* v_anonymous_1381_, lean_object* v_p_1382_){
_start:
{
uint8_t v_anonymous_boxed_1383_; lean_object* v_res_1384_; 
v_anonymous_boxed_1383_ = lean_unbox(v_anonymous_1381_);
v_res_1384_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1378_, v_kind_1379_, v_f_1380_, v_anonymous_boxed_1383_, v_p_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1385_, lean_object* v_kind_1386_, lean_object* v_f_1387_, uint8_t v_anonymous_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1394_ = 1;
v___x_1395_ = lean_box(v_anonymous_1388_);
v___x_1396_ = lean_box(v___x_1394_);
lean_inc(v_kind_1386_);
lean_inc_ref(v_name_1385_);
v___x_1397_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1397_, 0, v_name_1385_);
lean_closure_set(v___x_1397_, 1, v_kind_1386_);
lean_closure_set(v___x_1397_, 2, v___x_1395_);
lean_closure_set(v___x_1397_, 3, v___x_1396_);
v___x_1398_ = lean_box(v_anonymous_1388_);
v___x_1399_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1399_, 0, v_name_1385_);
lean_closure_set(v___x_1399_, 1, v_kind_1386_);
lean_closure_set(v___x_1399_, 2, v_f_1387_);
lean_closure_set(v___x_1399_, 3, v___x_1398_);
v___x_1400_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1400_, 0, v___x_1399_);
v___x_1401_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1397_, v___x_1400_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1402_, lean_object* v_kind_1403_, lean_object* v_f_1404_, lean_object* v_anonymous_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
uint8_t v_anonymous_boxed_1411_; lean_object* v_res_1412_; 
v_anonymous_boxed_1411_ = lean_unbox(v_anonymous_1405_);
v_res_1412_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1402_, v_kind_1403_, v_f_1404_, v_anonymous_boxed_1411_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1413_, lean_object* v_kind_1414_, lean_object* v_f_1415_, uint8_t v_anonymous_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1422_ = 1;
v___x_1423_ = lean_box(v_anonymous_1416_);
v___x_1424_ = lean_box(v___x_1422_);
lean_inc(v_kind_1414_);
lean_inc_ref(v_name_1413_);
v___x_1425_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1425_, 0, v_name_1413_);
lean_closure_set(v___x_1425_, 1, v_kind_1414_);
lean_closure_set(v___x_1425_, 2, v___x_1423_);
lean_closure_set(v___x_1425_, 3, v___x_1424_);
v___x_1426_ = lean_box(v_anonymous_1416_);
v___x_1427_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1427_, 0, v_name_1413_);
lean_closure_set(v___x_1427_, 1, v_kind_1414_);
lean_closure_set(v___x_1427_, 2, v_f_1415_);
lean_closure_set(v___x_1427_, 3, v___x_1426_);
v___x_1428_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1428_, 0, v___x_1427_);
v___x_1429_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1425_, v___x_1428_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1430_, lean_object* v_kind_1431_, lean_object* v_f_1432_, lean_object* v_anonymous_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
uint8_t v_anonymous_boxed_1439_; lean_object* v_res_1440_; 
v_anonymous_boxed_1439_ = lean_unbox(v_anonymous_1433_);
v_res_1440_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1430_, v_kind_1431_, v_f_1432_, v_anonymous_boxed_1439_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1441_, lean_object* v_kind_1442_, lean_object* v_f_1443_, uint8_t v_anonymous_1444_){
_start:
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1445_ = 1;
lean_inc_n(v_kind_1442_, 2);
lean_inc_ref(v_name_1441_);
v___x_1446_ = l_Lean_Parser_mkAntiquot(v_name_1441_, v_kind_1442_, v_anonymous_1444_, v___x_1445_);
v___x_1447_ = lean_box(v_anonymous_1444_);
v___x_1448_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1448_, 0, v_name_1441_);
lean_closure_set(v___x_1448_, 1, v_kind_1442_);
lean_closure_set(v___x_1448_, 2, v_f_1443_);
lean_closure_set(v___x_1448_, 3, v___x_1447_);
v___x_1449_ = l_Lake_Toml_recNode(v___x_1448_);
v___x_1450_ = l_Lean_Parser_withAntiquot(v___x_1446_, v___x_1449_);
v___x_1451_ = l_Lean_Parser_withCache(v_kind_1442_, v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1452_, lean_object* v_kind_1453_, lean_object* v_f_1454_, lean_object* v_anonymous_1455_){
_start:
{
uint8_t v_anonymous_boxed_1456_; lean_object* v_res_1457_; 
v_anonymous_boxed_1456_ = lean_unbox(v_anonymous_1455_);
v_res_1457_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1452_, v_kind_1453_, v_f_1454_, v_anonymous_boxed_1456_);
return v_res_1457_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___f_1465_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1466_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1467_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1467_, 0, v___x_1466_);
lean_closure_set(v___x_1467_, 1, v___f_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1474_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1475_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1476_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1476_, 0, v___x_1474_);
lean_closure_set(v___x_1476_, 1, v_p_1468_);
lean_closure_set(v___x_1476_, 2, v___x_1475_);
v___x_1477_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1478_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1476_, v___x_1477_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1486_, uint8_t v_allowTrailingLinebreak_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1486_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1494_, lean_object* v_allowTrailingLinebreak_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1501_; lean_object* v_res_1502_; 
v_allowTrailingLinebreak_boxed_1501_ = lean_unbox(v_allowTrailingLinebreak_1495_);
v_res_1502_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1494_, v_allowTrailingLinebreak_boxed_1501_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1502_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___f_1506_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1507_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1508_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1508_, 0, v___x_1507_);
lean_closure_set(v___x_1508_, 1, v___f_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1515_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1516_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1517_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1517_, 0, v___x_1515_);
lean_closure_set(v___x_1517_, 1, v_p_1509_);
lean_closure_set(v___x_1517_, 2, v___x_1516_);
v___x_1518_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1519_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1517_, v___x_1518_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1527_, uint8_t v_allowTrailingLinebreak_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1527_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1535_, lean_object* v_allowTrailingLinebreak_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1542_; lean_object* v_res_1543_; 
v_allowTrailingLinebreak_boxed_1542_ = lean_unbox(v_allowTrailingLinebreak_1536_);
v_res_1543_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1535_, v_allowTrailingLinebreak_boxed_1542_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1543_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1545_ = l_Lean_Parser_symbol(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1548_ = l_Lean_Parser_checkLinebreakBefore(v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = l_Lean_Parser_pushNone;
v___x_1550_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1551_ = l_Lean_Parser_andthen(v___x_1550_, v___x_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1552_, uint8_t v_allowTrailingLinebreak_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v_p_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1554_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1555_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1556_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1554_, v_p_1552_, v___x_1555_);
v___x_1557_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1558_ = l_Lean_Parser_sepByNoAntiquot(v_p_1556_, v___x_1557_, v_allowTrailingLinebreak_1553_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1559_, lean_object* v_allowTrailingLinebreak_1560_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1561_; lean_object* v_res_1562_; 
v_allowTrailingLinebreak_boxed_1561_ = lean_unbox(v_allowTrailingLinebreak_1560_);
v_res_1562_ = l_Lake_Toml_sepByLinebreak(v_p_1559_, v_allowTrailingLinebreak_boxed_1561_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1569_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1570_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1571_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1571_, 0, v___x_1569_);
lean_closure_set(v___x_1571_, 1, v_p_1563_);
lean_closure_set(v___x_1571_, 2, v___x_1570_);
v___x_1572_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1573_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1571_, v___x_1572_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1581_, uint8_t v_allowTrailingLinebreak_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1581_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1589_, lean_object* v_allowTrailingLinebreak_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1596_; lean_object* v_res_1597_; 
v_allowTrailingLinebreak_boxed_1596_ = lean_unbox(v_allowTrailingLinebreak_1590_);
v_res_1597_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1589_, v_allowTrailingLinebreak_boxed_1596_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1604_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1605_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1606_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1606_, 0, v___x_1604_);
lean_closure_set(v___x_1606_, 1, v_p_1598_);
lean_closure_set(v___x_1606_, 2, v___x_1605_);
v___x_1607_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1608_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1606_, v___x_1607_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1616_, uint8_t v_allowTrailingLinebreak_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1616_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1624_, lean_object* v_allowTrailingLinebreak_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1631_; lean_object* v_res_1632_; 
v_allowTrailingLinebreak_boxed_1631_ = lean_unbox(v_allowTrailingLinebreak_1625_);
v_res_1632_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1624_, v_allowTrailingLinebreak_boxed_1631_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1633_, uint8_t v_allowTrailingLinebreak_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_p_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1635_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1636_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1637_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1635_, v_p_1633_, v___x_1636_);
v___x_1638_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1639_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1637_, v___x_1638_, v_allowTrailingLinebreak_1634_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1640_, lean_object* v_allowTrailingLinebreak_1641_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1642_; lean_object* v_res_1643_; 
v_allowTrailingLinebreak_boxed_1642_ = lean_unbox(v_allowTrailingLinebreak_1641_);
v_res_1643_ = l_Lake_Toml_sepBy1Linebreak(v_p_1640_, v_allowTrailingLinebreak_boxed_1642_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1644_, lean_object* v_c_1645_, lean_object* v_s_1646_){
_start:
{
lean_object* v_toCacheableParserContext_1647_; lean_object* v_quotDepth_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_toCacheableParserContext_1647_ = lean_ctor_get(v_c_1645_, 2);
v_quotDepth_1648_ = lean_ctor_get(v_toCacheableParserContext_1647_, 1);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = lean_nat_dec_lt(v___x_1649_, v_quotDepth_1648_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_apply_2(v_p_1644_, v_c_1645_, v_s_1646_);
return v___x_1651_;
}
else
{
lean_dec_ref(v_c_1645_);
lean_dec_ref(v_p_1644_);
return v_s_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1658_; 
lean_inc(v_a_1656_);
lean_inc_ref(v_a_1655_);
lean_inc(v_a_1654_);
lean_inc_ref(v_a_1653_);
v___x_1658_ = lean_apply_5(v_p_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, lean_box(0));
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; 
lean_inc(v_a_1670_);
lean_inc_ref(v_a_1669_);
lean_inc(v_a_1668_);
lean_inc_ref(v_a_1667_);
v___x_1672_ = lean_apply_5(v_p_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, lean_box(0));
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1680_){
_start:
{
lean_object* v_info_1681_; lean_object* v_fn_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_info_1681_ = lean_ctor_get(v_p_1680_, 0);
v_fn_1682_ = lean_ctor_get(v_p_1680_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_p_1680_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v_p_1680_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_fn_1682_);
lean_inc(v_info_1681_);
lean_dec(v_p_1680_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1686_, 0, v_fn_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_info_1681_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_ParserUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
