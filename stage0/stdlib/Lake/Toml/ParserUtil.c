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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_430_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
lean_ctor_set(v___x_435_, 3, v___x_434_);
lean_ctor_set(v___x_435_, 4, v___x_433_);
lean_ctor_set(v___x_435_, 5, v___x_433_);
lean_ctor_set(v___x_435_, 6, v___x_433_);
lean_ctor_set(v___x_435_, 7, v___x_433_);
lean_ctor_set(v___x_435_, 8, v___x_433_);
lean_ctor_set(v___x_435_, 9, v___x_433_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_unsigned_to_nat(32u);
v___x_442_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3);
v___x_444_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_440_);
lean_ctor_set(v___x_444_, 3, v___x_440_);
lean_ctor_set_usize(v___x_444_, 4, v___x_439_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_box(1);
v___x_446_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4);
v___x_447_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(lean_object* v_msgData_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; lean_object* v_env_454_; lean_object* v_options_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_453_ = lean_st_ref_get(v___y_451_);
v_env_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc_ref(v_env_454_);
lean_dec(v___x_453_);
v_options_455_ = lean_ctor_get(v___y_450_, 2);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_455_);
v___x_458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_458_, 0, v_env_454_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set(v___x_458_, 3, v_options_455_);
v___x_459_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_msgData_449_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_465_;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_466_; double v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_float_of_nat(v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* v_cls_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_ref_475_; lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_521_; 
v_ref_475_ = lean_ctor_get(v___y_472_, 5);
v___x_476_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_471_, v___y_472_, v___y_473_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_521_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_521_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_521_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v_traceState_482_; lean_object* v_env_483_; lean_object* v_nextMacroScope_484_; lean_object* v_ngen_485_; lean_object* v_auxDeclNGen_486_; lean_object* v_cache_487_; lean_object* v_messages_488_; lean_object* v_infoState_489_; lean_object* v_snapshotTasks_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_520_; 
v___x_481_ = lean_st_ref_take(v___y_473_);
v_traceState_482_ = lean_ctor_get(v___x_481_, 4);
v_env_483_ = lean_ctor_get(v___x_481_, 0);
v_nextMacroScope_484_ = lean_ctor_get(v___x_481_, 1);
v_ngen_485_ = lean_ctor_get(v___x_481_, 2);
v_auxDeclNGen_486_ = lean_ctor_get(v___x_481_, 3);
v_cache_487_ = lean_ctor_get(v___x_481_, 5);
v_messages_488_ = lean_ctor_get(v___x_481_, 6);
v_infoState_489_ = lean_ctor_get(v___x_481_, 7);
v_snapshotTasks_490_ = lean_ctor_get(v___x_481_, 8);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_520_ == 0)
{
v___x_492_ = v___x_481_;
v_isShared_493_ = v_isSharedCheck_520_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snapshotTasks_490_);
lean_inc(v_infoState_489_);
lean_inc(v_messages_488_);
lean_inc(v_cache_487_);
lean_inc(v_traceState_482_);
lean_inc(v_auxDeclNGen_486_);
lean_inc(v_ngen_485_);
lean_inc(v_nextMacroScope_484_);
lean_inc(v_env_483_);
lean_dec(v___x_481_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_520_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
uint64_t v_tid_494_; lean_object* v_traces_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_519_; 
v_tid_494_ = lean_ctor_get_uint64(v_traceState_482_, sizeof(void*)*1);
v_traces_495_ = lean_ctor_get(v_traceState_482_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_traceState_482_);
if (v_isSharedCheck_519_ == 0)
{
v___x_497_ = v_traceState_482_;
v_isShared_498_ = v_isSharedCheck_519_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_traces_495_);
lean_dec(v_traceState_482_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_519_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; double v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_499_ = lean_box(0);
v___x_500_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_501_ = 0;
v___x_502_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_503_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_503_, 0, v_cls_470_);
lean_ctor_set(v___x_503_, 1, v___x_499_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
lean_ctor_set_float(v___x_503_, sizeof(void*)*3, v___x_500_);
lean_ctor_set_float(v___x_503_, sizeof(void*)*3 + 8, v___x_500_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*3 + 16, v___x_501_);
v___x_504_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_505_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v_a_477_);
lean_ctor_set(v___x_505_, 2, v___x_504_);
lean_inc(v_ref_475_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_ref_475_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_PersistentArray_push___redArg(v_traces_495_, v___x_506_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_507_);
v___x_509_ = v___x_497_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_507_);
lean_ctor_set_uint64(v_reuseFailAlloc_518_, sizeof(void*)*1, v_tid_494_);
v___x_509_ = v_reuseFailAlloc_518_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 4, v___x_509_);
v___x_511_ = v___x_492_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_env_483_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_nextMacroScope_484_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_ngen_485_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_auxDeclNGen_486_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v_cache_487_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_messages_488_);
lean_ctor_set(v_reuseFailAlloc_517_, 7, v_infoState_489_);
lean_ctor_set(v_reuseFailAlloc_517_, 8, v_snapshotTasks_490_);
v___x_511_ = v_reuseFailAlloc_517_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = lean_st_ref_set(v___y_473_, v___x_511_);
v___x_513_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_513_);
v___x_515_ = v___x_479_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_522_, lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_522_, v_msg_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_527_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_539_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__5));
v___x_540_ = l_Lean_Name_append(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__8(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__7));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__10(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__9));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v_a_553_; 
v___x_552_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_548_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref(v___x_552_);
if (lean_obj_tag(v_a_553_) == 2)
{
lean_object* v_info_554_; lean_object* v_val_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_info_554_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_info_554_);
v_val_555_ = lean_ctor_get(v_a_553_, 1);
lean_inc_ref(v_val_555_);
v___x_556_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_553_);
lean_dec_ref(v_a_553_);
v___x_557_ = 0;
v___x_558_ = lean_box(v___x_557_);
v___x_559_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_559_, 0, v_info_554_);
lean_closure_set(v___x_559_, 1, v_val_555_);
lean_closure_set(v___x_559_, 2, v___x_558_);
v___x_560_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_556_, v___x_559_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v___x_556_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; 
lean_dec_ref(v___x_560_);
v___x_561_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_548_);
return v___x_561_;
}
else
{
return v___x_560_;
}
}
else
{
lean_object* v_options_562_; uint8_t v_hasTrace_563_; 
v_options_562_ = lean_ctor_get(v_a_549_, 2);
v_hasTrace_563_ = lean_ctor_get_uint8(v_options_562_, sizeof(void*)*1);
if (v_hasTrace_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v_a_553_);
v___x_564_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_564_;
}
else
{
lean_object* v_inheritedTraceOptions_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_inheritedTraceOptions_565_ = lean_ctor_get(v_a_549_, 13);
v___x_566_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_567_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_565_, v_options_562_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v_a_553_);
v___x_569_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_570_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_571_ = lean_box(0);
v___x_572_ = 0;
v___x_573_ = l_Lean_Syntax_formatStx(v_a_553_, v___x_571_, v___x_572_);
v___x_574_ = l_Lean_MessageData_ofFormat(v___x_573_);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_570_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_566_, v___x_577_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_579_; 
lean_dec_ref(v___x_578_);
v___x_579_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_579_;
}
else
{
return v___x_578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lake_Toml_atom_formatter___redArg(v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lake_Toml_atom_formatter___redArg(v_a_588_, v_a_589_, v_a_590_, v_a_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lake_Toml_atom_formatter(v_x_594_, v_x_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec_ref(v_x_595_);
lean_dec_ref(v_x_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_602_, lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_602_, v_msg_603_, v___y_606_, v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_610_, lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_610_, v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_621_);
lean_dec(v_a_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_627_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_632_, v_x_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec_ref(v_x_633_);
lean_dec_ref(v_x_632_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_640_, lean_object* v_expected_641_, lean_object* v_trailingFn_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_box_uint32(v_c_640_);
v___x_644_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_644_, 0, v___x_643_);
lean_closure_set(v___x_644_, 1, v_expected_641_);
v___x_645_ = l_Lake_Toml_atom(v___x_644_, v_trailingFn_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_646_, lean_object* v_expected_647_, lean_object* v_trailingFn_648_){
_start:
{
uint32_t v_c_boxed_649_; lean_object* v_res_650_; 
v_c_boxed_649_ = lean_unbox_uint32(v_c_646_);
lean_dec(v_c_646_);
v_res_650_ = l_Lake_Toml_chAtom(v_c_boxed_649_, v_expected_647_, v_trailingFn_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
uint8_t v___x_657_; lean_object* v___x_658_; 
v___x_657_ = 0;
v___x_658_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_651_, v___x_657_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
uint32_t v_c_boxed_665_; lean_object* v_res_666_; 
v_c_boxed_665_ = lean_unbox_uint32(v_c_659_);
lean_dec(v_c_659_);
v_res_666_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_665_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_667_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
uint32_t v_c_boxed_684_; lean_object* v_res_685_; 
v_c_boxed_684_ = lean_unbox_uint32(v_c_676_);
lean_dec(v_c_676_);
v_res_685_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_684_, v_x_677_, v_x_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec_ref(v_x_678_);
lean_dec(v_x_677_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_689_);
lean_dec(v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_696_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
uint32_t v_x_18__boxed_709_; lean_object* v_res_710_; 
v_x_18__boxed_709_ = lean_unbox_uint32(v_x_701_);
lean_dec(v_x_701_);
v_res_710_ = l_Lake_Toml_chAtom_parenthesizer(v_x_18__boxed_709_, v_x_702_, v_x_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec_ref(v_x_703_);
lean_dec(v_x_702_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_711_, lean_object* v_expected_712_, lean_object* v_trailingFn_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_str_718_; lean_object* v_startInclusive_719_; lean_object* v_endExclusive_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_string_utf8_byte_size(v_s_711_);
v___x_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_716_, 0, v_s_711_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
v___x_717_ = l_String_Slice_trimAscii(v___x_716_);
v_str_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc_ref(v_str_718_);
v_startInclusive_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_startInclusive_719_);
v_endExclusive_720_ = lean_ctor_get(v___x_717_, 2);
lean_inc(v_endExclusive_720_);
lean_dec_ref(v___x_717_);
v___x_721_ = lean_string_utf8_extract(v_str_718_, v_startInclusive_719_, v_endExclusive_720_);
lean_dec(v_endExclusive_720_);
lean_dec(v_startInclusive_719_);
lean_dec_ref(v_str_718_);
v___x_722_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_722_, 0, v___x_721_);
lean_closure_set(v___x_722_, 1, v_expected_712_);
v___x_723_ = l_Lake_Toml_atom(v___x_722_, v_trailingFn_713_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_738_, lean_object* v_x_739_, lean_object* v_x_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_738_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lake_Toml_strAtom_formatter(v_s_747_, v_x_748_, v_x_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_x_749_);
lean_dec(v_x_748_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_759_);
lean_dec(v_a_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_766_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_Toml_strAtom_parenthesizer(v_x_771_, v_x_772_, v_x_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec_ref(v_x_773_);
lean_dec(v_x_772_);
lean_dec_ref(v_x_771_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_780_, lean_object* v_startPos_781_, lean_object* v_trailingFn_782_, lean_object* v_c_783_, lean_object* v_s_784_){
_start:
{
lean_object* v_toInputContext_785_; lean_object* v_pos_786_; lean_object* v_inputString_787_; lean_object* v_endPos_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_806_; 
v_toInputContext_785_ = lean_ctor_get(v_c_783_, 0);
lean_inc_ref(v_toInputContext_785_);
v_pos_786_ = lean_ctor_get(v_s_784_, 2);
lean_inc(v_pos_786_);
v_inputString_787_ = lean_ctor_get(v_toInputContext_785_, 0);
v_endPos_788_ = lean_ctor_get(v_toInputContext_785_, 3);
v_isSharedCheck_806_ = !lean_is_exclusive(v_toInputContext_785_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_807_ = lean_ctor_get(v_toInputContext_785_, 2);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_toInputContext_785_, 1);
lean_dec(v_unused_808_);
v___x_790_ = v_toInputContext_785_;
v_isShared_791_ = v_isSharedCheck_806_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_endPos_788_);
lean_inc(v_inputString_787_);
lean_dec(v_toInputContext_785_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_806_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_leading_792_; lean_object* v_s_793_; lean_object* v_pos_794_; lean_object* v_val_795_; lean_object* v___y_797_; uint8_t v___x_803_; 
lean_inc(v_startPos_781_);
v_leading_792_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_783_, v_startPos_781_);
v_s_793_ = lean_apply_2(v_trailingFn_782_, v_c_783_, v_s_784_);
v_pos_794_ = lean_ctor_get(v_s_793_, 2);
lean_inc(v_pos_794_);
v_val_795_ = lean_string_utf8_extract(v_inputString_787_, v_startPos_781_, v_pos_786_);
v___x_803_ = lean_nat_dec_le(v_pos_794_, v_endPos_788_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_pos_794_);
lean_inc(v_pos_786_);
v___x_804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_804_, 0, v_inputString_787_);
lean_ctor_set(v___x_804_, 1, v_pos_786_);
lean_ctor_set(v___x_804_, 2, v_endPos_788_);
v___y_797_ = v___x_804_;
goto v___jp_796_;
}
else
{
lean_object* v___x_805_; 
lean_dec(v_endPos_788_);
lean_inc(v_pos_786_);
v___x_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_805_, 0, v_inputString_787_);
lean_ctor_set(v___x_805_, 1, v_pos_786_);
lean_ctor_set(v___x_805_, 2, v_pos_794_);
v___y_797_ = v___x_805_;
goto v___jp_796_;
}
v___jp_796_:
{
lean_object* v_info_799_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 3, v_pos_786_);
lean_ctor_set(v___x_790_, 2, v___y_797_);
lean_ctor_set(v___x_790_, 1, v_startPos_781_);
lean_ctor_set(v___x_790_, 0, v_leading_792_);
v_info_799_ = v___x_790_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_leading_792_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_startPos_781_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v___y_797_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_pos_786_);
v_info_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = l_Lean_Syntax_mkLit(v_kind_780_, v_val_795_, v_info_799_);
v___x_801_ = l_Lean_Parser_ParserState_pushSyntax(v_s_793_, v___x_800_);
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_809_, lean_object* v_p_810_, lean_object* v_trailingFn_811_, lean_object* v_c_812_, lean_object* v_s_813_){
_start:
{
lean_object* v_pos_814_; lean_object* v_s_815_; lean_object* v_errorMsg_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_pos_814_ = lean_ctor_get(v_s_813_, 2);
lean_inc(v_pos_814_);
lean_inc_ref(v_c_812_);
v_s_815_ = lean_apply_2(v_p_810_, v_c_812_, v_s_813_);
v_errorMsg_816_ = lean_ctor_get(v_s_815_, 4);
lean_inc(v_errorMsg_816_);
v___x_817_ = lean_box(0);
v___x_818_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_dec(v_pos_814_);
lean_dec_ref(v_c_812_);
lean_dec_ref(v_trailingFn_811_);
lean_dec(v_kind_809_);
return v_s_815_;
}
else
{
lean_object* v___x_819_; 
v___x_819_ = l_Lake_Toml_pushLit(v_kind_809_, v_pos_814_, v_trailingFn_811_, v_c_812_, v_s_815_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_820_, lean_object* v_p_821_, lean_object* v_trailingFn_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_824_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_824_, 0, v_kind_820_);
lean_closure_set(v___x_824_, 1, v_p_821_);
lean_closure_set(v___x_824_, 2, v_trailingFn_822_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_Toml_lit_formatter___redArg(v_kind_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_840_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lake_Toml_lit_formatter(v_kind_849_, v_x_850_, v_x_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec_ref(v_x_851_);
lean_dec_ref(v_x_850_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_861_);
lean_dec(v_a_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_868_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lake_Toml_lit_parenthesizer(v_x_873_, v_x_874_, v_x_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec_ref(v_x_875_);
lean_dec_ref(v_x_874_);
lean_dec(v_x_873_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_896_, lean_object* v_kind_897_, uint8_t v_anonymous_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___f_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_inc(v_kind_897_);
v___f_904_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_904_, 0, v_kind_897_);
v___x_905_ = 0;
v___x_906_ = lean_box(v_anonymous_898_);
v___x_907_ = lean_box(v___x_905_);
v___x_908_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_908_, 0, v_name_896_);
lean_closure_set(v___x_908_, 1, v_kind_897_);
lean_closure_set(v___x_908_, 2, v___x_906_);
lean_closure_set(v___x_908_, 3, v___x_907_);
v___x_909_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_908_, v___f_904_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_910_, lean_object* v_kind_911_, lean_object* v_anonymous_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
uint8_t v_anonymous_boxed_918_; lean_object* v_res_919_; 
v_anonymous_boxed_918_ = lean_unbox(v_anonymous_912_);
v_res_919_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_910_, v_kind_911_, v_anonymous_boxed_918_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_920_, lean_object* v_kind_921_, lean_object* v_p_922_, lean_object* v_trailingFn_923_, uint8_t v_anonymous_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_920_, v_kind_921_, v_anonymous_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_931_, lean_object* v_kind_932_, lean_object* v_p_933_, lean_object* v_trailingFn_934_, lean_object* v_anonymous_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_anonymous_boxed_941_; lean_object* v_res_942_; 
v_anonymous_boxed_941_ = lean_unbox(v_anonymous_935_);
v_res_942_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_931_, v_kind_932_, v_p_933_, v_trailingFn_934_, v_anonymous_boxed_941_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec_ref(v_trailingFn_934_);
lean_dec_ref(v_p_933_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_944_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_956_, lean_object* v_kind_957_, uint8_t v_anonymous_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___f_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___f_964_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_965_ = 0;
v___x_966_ = lean_box(v_anonymous_958_);
v___x_967_ = lean_box(v___x_965_);
v___x_968_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_968_, 0, v_name_956_);
lean_closure_set(v___x_968_, 1, v_kind_957_);
lean_closure_set(v___x_968_, 2, v___x_966_);
lean_closure_set(v___x_968_, 3, v___x_967_);
v___x_969_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_968_, v___f_964_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_970_, lean_object* v_kind_971_, lean_object* v_anonymous_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
uint8_t v_anonymous_boxed_978_; lean_object* v_res_979_; 
v_anonymous_boxed_978_ = lean_unbox(v_anonymous_972_);
v_res_979_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_970_, v_kind_971_, v_anonymous_boxed_978_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_980_, lean_object* v_kind_981_, lean_object* v_p_982_, lean_object* v_trailingFn_983_, uint8_t v_anonymous_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_980_, v_kind_981_, v_anonymous_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_991_, lean_object* v_kind_992_, lean_object* v_p_993_, lean_object* v_trailingFn_994_, lean_object* v_anonymous_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
uint8_t v_anonymous_boxed_1001_; lean_object* v_res_1002_; 
v_anonymous_boxed_1001_ = lean_unbox(v_anonymous_995_);
v_res_1002_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_991_, v_kind_992_, v_p_993_, v_trailingFn_994_, v_anonymous_boxed_1001_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec_ref(v_trailingFn_994_);
lean_dec_ref(v_p_993_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1003_, lean_object* v_kind_1004_, lean_object* v_p_1005_, lean_object* v_trailingFn_1006_, uint8_t v_anonymous_1007_){
_start:
{
uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = 0;
lean_inc(v_kind_1004_);
v___x_1009_ = l_Lean_Parser_mkAntiquot(v_name_1003_, v_kind_1004_, v_anonymous_1007_, v___x_1008_);
v___x_1010_ = l_Lake_Toml_lit(v_kind_1004_, v_p_1005_, v_trailingFn_1006_);
v___x_1011_ = l_Lean_Parser_withAntiquot(v___x_1009_, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1012_, lean_object* v_kind_1013_, lean_object* v_p_1014_, lean_object* v_trailingFn_1015_, lean_object* v_anonymous_1016_){
_start:
{
uint8_t v_anonymous_boxed_1017_; lean_object* v_res_1018_; 
v_anonymous_boxed_1017_ = lean_unbox(v_anonymous_1016_);
v_res_1018_ = l_Lake_Toml_litWithAntiquot(v_name_1012_, v_kind_1013_, v_p_1014_, v_trailingFn_1015_, v_anonymous_boxed_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = l_Lean_Parser_epsilonInfo;
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v_fn_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lake_Toml_epsilon_formatter(v_x_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec_ref(v_x_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_x_1053_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1060_, lean_object* v_x_1061_){
_start:
{
switch(lean_obj_tag(v_x_1061_))
{
case 2:
{
lean_object* v_info_1062_; lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_info_1062_ = lean_ctor_get(v_x_1061_, 0);
v_val_1063_ = lean_ctor_get(v_x_1061_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1061_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v_x_1061_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_inc(v_info_1062_);
lean_dec(v_x_1061_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_apply_1(v_f_1060_, v_info_1062_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_val_1063_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
case 3:
{
lean_object* v_info_1072_; lean_object* v_rawVal_1073_; lean_object* v_val_1074_; lean_object* v_preresolved_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_info_1072_ = lean_ctor_get(v_x_1061_, 0);
v_rawVal_1073_ = lean_ctor_get(v_x_1061_, 1);
v_val_1074_ = lean_ctor_get(v_x_1061_, 2);
v_preresolved_1075_ = lean_ctor_get(v_x_1061_, 3);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_1061_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_x_1061_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_preresolved_1075_);
lean_inc(v_val_1074_);
lean_inc(v_rawVal_1073_);
lean_inc(v_info_1072_);
lean_dec(v_x_1061_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_apply_1(v_f_1060_, v_info_1072_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_rawVal_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_val_1074_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_preresolved_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
case 1:
{
lean_object* v_info_1084_; lean_object* v_kind_1085_; lean_object* v_args_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_info_1084_ = lean_ctor_get(v_x_1061_, 0);
v_kind_1085_ = lean_ctor_get(v_x_1061_, 1);
v_args_1086_ = lean_ctor_get(v_x_1061_, 2);
v___x_1087_ = lean_array_get_size(v_args_1086_);
v___x_1088_ = lean_unsigned_to_nat(1u);
v___x_1089_ = lean_nat_sub(v___x_1087_, v___x_1088_);
v___x_1090_ = lean_nat_dec_lt(v___x_1089_, v___x_1087_);
if (v___x_1090_ == 0)
{
lean_dec(v___x_1089_);
lean_dec_ref(v_f_1060_);
return v_x_1061_;
}
else
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1102_; 
lean_inc_ref(v_args_1086_);
lean_inc(v_kind_1085_);
lean_inc(v_info_1084_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1061_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1103_ = lean_ctor_get(v_x_1061_, 2);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_x_1061_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_x_1061_, 0);
lean_dec(v_unused_1105_);
v___x_1092_ = v_x_1061_;
v_isShared_1093_ = v_isSharedCheck_1102_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_x_1061_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1102_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_v_1094_; lean_object* v___x_1095_; lean_object* v_xs_x27_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v_v_1094_ = lean_array_fget(v_args_1086_, v___x_1089_);
v___x_1095_ = lean_box(0);
v_xs_x27_1096_ = lean_array_fset(v_args_1086_, v___x_1089_, v___x_1095_);
v___x_1097_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1060_, v_v_1094_);
v___x_1098_ = lean_array_fset(v_xs_x27_1096_, v___x_1089_, v___x_1097_);
lean_dec(v___x_1089_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 2, v___x_1098_);
v___x_1100_ = v___x_1092_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_info_1084_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_kind_1085_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1060_);
return v_x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1106_, lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_object* v_trailing_1108_; lean_object* v_leading_1109_; lean_object* v_pos_1110_; lean_object* v_endPos_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1128_; 
v_trailing_1108_ = lean_ctor_get(v_x_1107_, 2);
v_leading_1109_ = lean_ctor_get(v_x_1107_, 0);
v_pos_1110_ = lean_ctor_get(v_x_1107_, 1);
v_endPos_1111_ = lean_ctor_get(v_x_1107_, 3);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1113_ = v_x_1107_;
v_isShared_1114_ = v_isSharedCheck_1128_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_endPos_1111_);
lean_inc(v_trailing_1108_);
lean_inc(v_pos_1110_);
lean_inc(v_leading_1109_);
lean_dec(v_x_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1128_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_str_1115_; lean_object* v_startPos_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1126_; 
v_str_1115_ = lean_ctor_get(v_trailing_1108_, 0);
v_startPos_1116_ = lean_ctor_get(v_trailing_1108_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_trailing_1108_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_trailing_1108_, 2);
lean_dec(v_unused_1127_);
v___x_1118_ = v_trailing_1108_;
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_startPos_1116_);
lean_inc(v_str_1115_);
lean_dec(v_trailing_1108_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 2, v_stopPos_1106_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_str_1115_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_startPos_1116_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_stopPos_1106_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 2, v___x_1121_);
v___x_1123_ = v___x_1113_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_leading_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_pos_1110_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_endPos_1111_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
else
{
lean_dec(v_stopPos_1106_);
return v_x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1129_, lean_object* v_x_1130_){
_start:
{
switch(lean_obj_tag(v_x_1130_))
{
case 2:
{
lean_object* v_info_1131_; lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v_info_1131_ = lean_ctor_get(v_x_1130_, 0);
v_val_1132_ = lean_ctor_get(v_x_1130_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1130_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1134_ = v_x_1130_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_inc(v_info_1131_);
lean_dec(v_x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1129_, v_info_1131_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_val_1132_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
case 3:
{
lean_object* v_info_1141_; lean_object* v_rawVal_1142_; lean_object* v_val_1143_; lean_object* v_preresolved_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_info_1141_ = lean_ctor_get(v_x_1130_, 0);
v_rawVal_1142_ = lean_ctor_get(v_x_1130_, 1);
v_val_1143_ = lean_ctor_get(v_x_1130_, 2);
v_preresolved_1144_ = lean_ctor_get(v_x_1130_, 3);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_x_1130_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v_x_1130_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_preresolved_1144_);
lean_inc(v_val_1143_);
lean_inc(v_rawVal_1142_);
lean_inc(v_info_1141_);
lean_dec(v_x_1130_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1129_, v_info_1141_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_rawVal_1142_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_val_1143_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_preresolved_1144_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
case 1:
{
lean_object* v_info_1153_; lean_object* v_kind_1154_; lean_object* v_args_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_info_1153_ = lean_ctor_get(v_x_1130_, 0);
v_kind_1154_ = lean_ctor_get(v_x_1130_, 1);
v_args_1155_ = lean_ctor_get(v_x_1130_, 2);
v___x_1156_ = lean_array_get_size(v_args_1155_);
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_sub(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_nat_dec_lt(v___x_1158_, v___x_1156_);
if (v___x_1159_ == 0)
{
lean_dec(v___x_1158_);
lean_dec(v_stopPos_1129_);
return v_x_1130_;
}
else
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1171_; 
lean_inc_ref(v_args_1155_);
lean_inc(v_kind_1154_);
lean_inc(v_info_1153_);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1130_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1172_ = lean_ctor_get(v_x_1130_, 2);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_x_1130_, 1);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_x_1130_, 0);
lean_dec(v_unused_1174_);
v___x_1161_ = v_x_1130_;
v_isShared_1162_ = v_isSharedCheck_1171_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_x_1130_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1171_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_v_1163_; lean_object* v___x_1164_; lean_object* v_xs_x27_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v_v_1163_ = lean_array_fget(v_args_1155_, v___x_1158_);
v___x_1164_ = lean_box(0);
v_xs_x27_1165_ = lean_array_fset(v_args_1155_, v___x_1158_, v___x_1164_);
v___x_1166_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1129_, v_v_1163_);
v___x_1167_ = lean_array_fset(v_xs_x27_1165_, v___x_1158_, v___x_1166_);
lean_dec(v___x_1158_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v___x_1167_);
v___x_1169_ = v___x_1161_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_info_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_kind_1154_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1129_);
return v_x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1175_, lean_object* v_c_1176_, lean_object* v_s_1177_){
_start:
{
lean_object* v_s_1178_; lean_object* v_stxStack_1179_; lean_object* v_pos_1180_; lean_object* v_tail_1181_; lean_object* v_s_1182_; lean_object* v_tail_1183_; lean_object* v___x_1184_; 
v_s_1178_ = lean_apply_2(v_p_1175_, v_c_1176_, v_s_1177_);
v_stxStack_1179_ = lean_ctor_get(v_s_1178_, 0);
lean_inc_ref(v_stxStack_1179_);
v_pos_1180_ = lean_ctor_get(v_s_1178_, 2);
lean_inc(v_pos_1180_);
v_tail_1181_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1179_);
lean_dec_ref(v_stxStack_1179_);
v_s_1182_ = l_Lean_Parser_ParserState_popSyntax(v_s_1178_);
v_tail_1183_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1180_, v_tail_1181_);
v___x_1184_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1182_, v_tail_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lake_Toml_trailing_formatter(v_p_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec_ref(v_p_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lake_Toml_trailing_parenthesizer(v_p_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec_ref(v_p_1214_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1222_, 0, v_p_1221_);
v___x_1223_ = l_Lean_Parser_epsilonInfo;
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___x_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_p_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v_a_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1229_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = l_Lean_Syntax_getKind(v_a_1234_);
v___x_1236_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1235_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lake_Toml_dynamicNode_formatter(v_x_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec_ref(v_x_1250_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v_stxTrav_1260_; lean_object* v_cur_1261_; lean_object* v___x_1262_; 
v___x_1259_ = lean_st_ref_get(v___y_1257_);
v_stxTrav_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_stxTrav_1260_);
lean_dec(v___x_1259_);
v_cur_1261_ = lean_ctor_get(v_stxTrav_1260_, 0);
lean_inc(v_cur_1261_);
lean_dec_ref(v_stxTrav_1260_);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_cur_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1267_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1279_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_Syntax_getKind(v_a_1284_);
v___x_1286_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1285_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec_ref(v_x_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_fn_1313_; lean_object* v___x_1314_; 
lean_inc_ref(v_f_1307_);
v___x_1310_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1310_, 0, v_f_1307_);
v___x_1311_ = l_Lake_Toml_dynamicNode(v___x_1310_);
v___x_1312_ = lean_apply_1(v_f_1307_, v___x_1311_);
v_fn_1313_ = lean_ctor_get(v___x_1312_, 1);
lean_inc_ref(v_fn_1313_);
lean_dec_ref(v___x_1312_);
v___x_1314_ = lean_apply_2(v_fn_1313_, v_a_1308_, v_a_1309_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lake_Toml_recNode_formatter(v_f_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec_ref(v_f_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lake_Toml_recNode_parenthesizer(v_f_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v_f_1360_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1368_, 0, v_f_1367_);
v___x_1369_ = l_Lake_Toml_dynamicNode(v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1370_, lean_object* v_kind_1371_, lean_object* v_f_1372_, uint8_t v_anonymous_1373_, lean_object* v_p_1374_){
_start:
{
uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1375_ = 1;
lean_inc(v_kind_1371_);
v___x_1376_ = l_Lean_Parser_mkAntiquot(v_name_1370_, v_kind_1371_, v_anonymous_1373_, v___x_1375_);
v___x_1377_ = lean_apply_1(v_f_1372_, v_p_1374_);
v___x_1378_ = l_Lean_Parser_withAntiquot(v___x_1376_, v___x_1377_);
v___x_1379_ = l_Lean_Parser_withCache(v_kind_1371_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1380_, lean_object* v_kind_1381_, lean_object* v_f_1382_, lean_object* v_anonymous_1383_, lean_object* v_p_1384_){
_start:
{
uint8_t v_anonymous_boxed_1385_; lean_object* v_res_1386_; 
v_anonymous_boxed_1385_ = lean_unbox(v_anonymous_1383_);
v_res_1386_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1380_, v_kind_1381_, v_f_1382_, v_anonymous_boxed_1385_, v_p_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1387_, lean_object* v_kind_1388_, lean_object* v_f_1389_, uint8_t v_anonymous_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1396_ = 1;
v___x_1397_ = lean_box(v_anonymous_1390_);
v___x_1398_ = lean_box(v___x_1396_);
lean_inc(v_kind_1388_);
lean_inc_ref(v_name_1387_);
v___x_1399_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1399_, 0, v_name_1387_);
lean_closure_set(v___x_1399_, 1, v_kind_1388_);
lean_closure_set(v___x_1399_, 2, v___x_1397_);
lean_closure_set(v___x_1399_, 3, v___x_1398_);
v___x_1400_ = lean_box(v_anonymous_1390_);
v___x_1401_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1401_, 0, v_name_1387_);
lean_closure_set(v___x_1401_, 1, v_kind_1388_);
lean_closure_set(v___x_1401_, 2, v_f_1389_);
lean_closure_set(v___x_1401_, 3, v___x_1400_);
v___x_1402_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1402_, 0, v___x_1401_);
v___x_1403_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1399_, v___x_1402_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1404_, lean_object* v_kind_1405_, lean_object* v_f_1406_, lean_object* v_anonymous_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
uint8_t v_anonymous_boxed_1413_; lean_object* v_res_1414_; 
v_anonymous_boxed_1413_ = lean_unbox(v_anonymous_1407_);
v_res_1414_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1404_, v_kind_1405_, v_f_1406_, v_anonymous_boxed_1413_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1415_, lean_object* v_kind_1416_, lean_object* v_f_1417_, uint8_t v_anonymous_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1424_ = 1;
v___x_1425_ = lean_box(v_anonymous_1418_);
v___x_1426_ = lean_box(v___x_1424_);
lean_inc(v_kind_1416_);
lean_inc_ref(v_name_1415_);
v___x_1427_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1427_, 0, v_name_1415_);
lean_closure_set(v___x_1427_, 1, v_kind_1416_);
lean_closure_set(v___x_1427_, 2, v___x_1425_);
lean_closure_set(v___x_1427_, 3, v___x_1426_);
v___x_1428_ = lean_box(v_anonymous_1418_);
v___x_1429_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1429_, 0, v_name_1415_);
lean_closure_set(v___x_1429_, 1, v_kind_1416_);
lean_closure_set(v___x_1429_, 2, v_f_1417_);
lean_closure_set(v___x_1429_, 3, v___x_1428_);
v___x_1430_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1430_, 0, v___x_1429_);
v___x_1431_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1427_, v___x_1430_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1432_, lean_object* v_kind_1433_, lean_object* v_f_1434_, lean_object* v_anonymous_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
uint8_t v_anonymous_boxed_1441_; lean_object* v_res_1442_; 
v_anonymous_boxed_1441_ = lean_unbox(v_anonymous_1435_);
v_res_1442_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1432_, v_kind_1433_, v_f_1434_, v_anonymous_boxed_1441_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1443_, lean_object* v_kind_1444_, lean_object* v_f_1445_, uint8_t v_anonymous_1446_){
_start:
{
uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1447_ = 1;
lean_inc_n(v_kind_1444_, 2);
lean_inc_ref(v_name_1443_);
v___x_1448_ = l_Lean_Parser_mkAntiquot(v_name_1443_, v_kind_1444_, v_anonymous_1446_, v___x_1447_);
v___x_1449_ = lean_box(v_anonymous_1446_);
v___x_1450_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1450_, 0, v_name_1443_);
lean_closure_set(v___x_1450_, 1, v_kind_1444_);
lean_closure_set(v___x_1450_, 2, v_f_1445_);
lean_closure_set(v___x_1450_, 3, v___x_1449_);
v___x_1451_ = l_Lake_Toml_recNode(v___x_1450_);
v___x_1452_ = l_Lean_Parser_withAntiquot(v___x_1448_, v___x_1451_);
v___x_1453_ = l_Lean_Parser_withCache(v_kind_1444_, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1454_, lean_object* v_kind_1455_, lean_object* v_f_1456_, lean_object* v_anonymous_1457_){
_start:
{
uint8_t v_anonymous_boxed_1458_; lean_object* v_res_1459_; 
v_anonymous_boxed_1458_ = lean_unbox(v_anonymous_1457_);
v_res_1459_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1454_, v_kind_1455_, v_f_1456_, v_anonymous_boxed_1458_);
return v_res_1459_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___f_1467_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1468_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1469_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1469_, 0, v___x_1468_);
lean_closure_set(v___x_1469_, 1, v___f_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1476_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1477_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1478_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1478_, 0, v___x_1476_);
lean_closure_set(v___x_1478_, 1, v_p_1470_);
lean_closure_set(v___x_1478_, 2, v___x_1477_);
v___x_1479_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1480_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1478_, v___x_1479_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1488_, uint8_t v_allowTrailingLinebreak_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1488_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1496_, lean_object* v_allowTrailingLinebreak_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1503_; lean_object* v_res_1504_; 
v_allowTrailingLinebreak_boxed_1503_ = lean_unbox(v_allowTrailingLinebreak_1497_);
v_res_1504_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1496_, v_allowTrailingLinebreak_boxed_1503_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1504_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___f_1508_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1509_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1510_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1510_, 0, v___x_1509_);
lean_closure_set(v___x_1510_, 1, v___f_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1518_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1519_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1519_, 0, v___x_1517_);
lean_closure_set(v___x_1519_, 1, v_p_1511_);
lean_closure_set(v___x_1519_, 2, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1521_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1519_, v___x_1520_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1529_, uint8_t v_allowTrailingLinebreak_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1529_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1537_, lean_object* v_allowTrailingLinebreak_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1544_; lean_object* v_res_1545_; 
v_allowTrailingLinebreak_boxed_1544_ = lean_unbox(v_allowTrailingLinebreak_1538_);
v_res_1545_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1537_, v_allowTrailingLinebreak_boxed_1544_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1547_ = l_Lean_Parser_symbol(v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1550_ = l_Lean_Parser_checkLinebreakBefore(v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = l_Lean_Parser_pushNone;
v___x_1552_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1553_ = l_Lean_Parser_andthen(v___x_1552_, v___x_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1554_, uint8_t v_allowTrailingLinebreak_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_p_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1556_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1557_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1558_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1556_, v_p_1554_, v___x_1557_);
v___x_1559_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1560_ = l_Lean_Parser_sepByNoAntiquot(v_p_1558_, v___x_1559_, v_allowTrailingLinebreak_1555_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1561_, lean_object* v_allowTrailingLinebreak_1562_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1563_; lean_object* v_res_1564_; 
v_allowTrailingLinebreak_boxed_1563_ = lean_unbox(v_allowTrailingLinebreak_1562_);
v_res_1564_ = l_Lake_Toml_sepByLinebreak(v_p_1561_, v_allowTrailingLinebreak_boxed_1563_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1572_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1573_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1573_, 0, v___x_1571_);
lean_closure_set(v___x_1573_, 1, v_p_1565_);
lean_closure_set(v___x_1573_, 2, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1575_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1573_, v___x_1574_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1583_, uint8_t v_allowTrailingLinebreak_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1583_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1591_, lean_object* v_allowTrailingLinebreak_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1598_; lean_object* v_res_1599_; 
v_allowTrailingLinebreak_boxed_1598_ = lean_unbox(v_allowTrailingLinebreak_1592_);
v_res_1599_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1591_, v_allowTrailingLinebreak_boxed_1598_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1606_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1607_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1608_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1608_, 0, v___x_1606_);
lean_closure_set(v___x_1608_, 1, v_p_1600_);
lean_closure_set(v___x_1608_, 2, v___x_1607_);
v___x_1609_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1610_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1608_, v___x_1609_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1618_, uint8_t v_allowTrailingLinebreak_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1618_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1626_, lean_object* v_allowTrailingLinebreak_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1633_; lean_object* v_res_1634_; 
v_allowTrailingLinebreak_boxed_1633_ = lean_unbox(v_allowTrailingLinebreak_1627_);
v_res_1634_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1626_, v_allowTrailingLinebreak_boxed_1633_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1635_, uint8_t v_allowTrailingLinebreak_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_p_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1637_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1638_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1639_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1637_, v_p_1635_, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1641_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1639_, v___x_1640_, v_allowTrailingLinebreak_1636_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1642_, lean_object* v_allowTrailingLinebreak_1643_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1644_; lean_object* v_res_1645_; 
v_allowTrailingLinebreak_boxed_1644_ = lean_unbox(v_allowTrailingLinebreak_1643_);
v_res_1645_ = l_Lake_Toml_sepBy1Linebreak(v_p_1642_, v_allowTrailingLinebreak_boxed_1644_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1646_, lean_object* v_c_1647_, lean_object* v_s_1648_){
_start:
{
lean_object* v_toCacheableParserContext_1649_; lean_object* v_quotDepth_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_toCacheableParserContext_1649_ = lean_ctor_get(v_c_1647_, 2);
v_quotDepth_1650_ = lean_ctor_get(v_toCacheableParserContext_1649_, 1);
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_nat_dec_lt(v___x_1651_, v_quotDepth_1650_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_apply_2(v_p_1646_, v_c_1647_, v_s_1648_);
return v___x_1653_;
}
else
{
lean_dec_ref(v_c_1647_);
lean_dec_ref(v_p_1646_);
return v_s_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1660_; 
lean_inc(v_a_1658_);
lean_inc_ref(v_a_1657_);
lean_inc(v_a_1656_);
lean_inc_ref(v_a_1655_);
v___x_1660_ = lean_apply_5(v_p_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, lean_box(0));
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; 
lean_inc(v_a_1672_);
lean_inc_ref(v_a_1671_);
lean_inc(v_a_1670_);
lean_inc_ref(v_a_1669_);
v___x_1674_ = lean_apply_5(v_p_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, lean_box(0));
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1682_){
_start:
{
lean_object* v_info_1683_; lean_object* v_fn_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_info_1683_ = lean_ctor_get(v_p_1682_, 0);
v_fn_1684_ = lean_ctor_get(v_p_1682_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_p_1682_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v_p_1682_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_fn_1684_);
lean_inc(v_info_1683_);
lean_dec(v_p_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1688_, 0, v_fn_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_info_1683_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
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
