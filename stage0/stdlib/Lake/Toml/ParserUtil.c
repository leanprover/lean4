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
lean_object* v_ref_475_; lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_522_; 
v_ref_475_ = lean_ctor_get(v___y_472_, 5);
v___x_476_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_471_, v___y_472_, v___y_473_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_522_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_522_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_522_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v_traceState_482_; lean_object* v_env_483_; lean_object* v_nextMacroScope_484_; lean_object* v_ngen_485_; lean_object* v_auxDeclNGen_486_; lean_object* v_cache_487_; lean_object* v_messages_488_; lean_object* v_infoState_489_; lean_object* v_snapshotTasks_490_; lean_object* v_newDecls_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_521_; 
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
v_newDecls_491_ = lean_ctor_get(v___x_481_, 9);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_521_ == 0)
{
v___x_493_ = v___x_481_;
v_isShared_494_ = v_isSharedCheck_521_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_newDecls_491_);
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
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_521_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint64_t v_tid_495_; lean_object* v_traces_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_520_; 
v_tid_495_ = lean_ctor_get_uint64(v_traceState_482_, sizeof(void*)*1);
v_traces_496_ = lean_ctor_get(v_traceState_482_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_traceState_482_);
if (v_isSharedCheck_520_ == 0)
{
v___x_498_ = v_traceState_482_;
v_isShared_499_ = v_isSharedCheck_520_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_traces_496_);
lean_dec(v_traceState_482_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_520_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; double v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_500_ = lean_box(0);
v___x_501_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_502_ = 0;
v___x_503_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_504_, 0, v_cls_470_);
lean_ctor_set(v___x_504_, 1, v___x_500_);
lean_ctor_set(v___x_504_, 2, v___x_503_);
lean_ctor_set_float(v___x_504_, sizeof(void*)*3, v___x_501_);
lean_ctor_set_float(v___x_504_, sizeof(void*)*3 + 8, v___x_501_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3 + 16, v___x_502_);
v___x_505_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_506_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v_a_477_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
lean_inc(v_ref_475_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_ref_475_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = l_Lean_PersistentArray_push___redArg(v_traces_496_, v___x_507_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_508_);
v___x_510_ = v___x_498_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_508_);
lean_ctor_set_uint64(v_reuseFailAlloc_519_, sizeof(void*)*1, v_tid_495_);
v___x_510_ = v_reuseFailAlloc_519_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v___x_510_);
v___x_512_ = v___x_493_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_env_483_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_nextMacroScope_484_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_ngen_485_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_auxDeclNGen_486_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v_cache_487_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_messages_488_);
lean_ctor_set(v_reuseFailAlloc_518_, 7, v_infoState_489_);
lean_ctor_set(v_reuseFailAlloc_518_, 8, v_snapshotTasks_490_);
lean_ctor_set(v_reuseFailAlloc_518_, 9, v_newDecls_491_);
v___x_512_ = v_reuseFailAlloc_518_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = lean_st_ref_set(v___y_473_, v___x_512_);
v___x_514_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_514_);
v___x_516_ = v___x_479_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_523_, lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_523_, v_msg_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_528_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_540_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__5));
v___x_541_ = l_Lean_Name_append(v___x_540_, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__8(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__7));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__10(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__9));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_a_554_; 
v___x_553_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_549_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
if (lean_obj_tag(v_a_554_) == 2)
{
lean_object* v_info_555_; lean_object* v_val_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_info_555_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_info_555_);
v_val_556_ = lean_ctor_get(v_a_554_, 1);
lean_inc_ref(v_val_556_);
v___x_557_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_554_);
lean_dec_ref(v_a_554_);
v___x_558_ = 0;
v___x_559_ = lean_box(v___x_558_);
v___x_560_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_560_, 0, v_info_555_);
lean_closure_set(v___x_560_, 1, v_val_556_);
lean_closure_set(v___x_560_, 2, v___x_559_);
v___x_561_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_557_, v___x_560_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v___x_557_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; 
lean_dec_ref(v___x_561_);
v___x_562_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_549_);
return v___x_562_;
}
else
{
return v___x_561_;
}
}
else
{
lean_object* v_options_563_; uint8_t v_hasTrace_564_; 
v_options_563_ = lean_ctor_get(v_a_550_, 2);
v_hasTrace_564_ = lean_ctor_get_uint8(v_options_563_, sizeof(void*)*1);
if (v_hasTrace_564_ == 0)
{
lean_object* v___x_565_; 
lean_dec(v_a_554_);
v___x_565_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_565_;
}
else
{
lean_object* v_inheritedTraceOptions_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_inheritedTraceOptions_566_ = lean_ctor_get(v_a_550_, 13);
v___x_567_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_568_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_566_, v_options_563_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v_a_554_);
v___x_570_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_571_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_572_ = lean_box(0);
v___x_573_ = 0;
v___x_574_ = l_Lean_Syntax_formatStx(v_a_554_, v___x_572_, v___x_573_);
v___x_575_ = l_Lean_MessageData_ofFormat(v___x_574_);
v___x_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_571_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_567_, v___x_578_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; 
lean_dec_ref(v___x_579_);
v___x_580_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_580_;
}
else
{
return v___x_579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lake_Toml_atom_formatter___redArg(v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lake_Toml_atom_formatter___redArg(v_a_589_, v_a_590_, v_a_591_, v_a_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lake_Toml_atom_formatter(v_x_595_, v_x_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v_x_596_);
lean_dec_ref(v_x_595_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_603_, lean_object* v_msg_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_603_, v_msg_604_, v___y_607_, v___y_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_611_, lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_611_, v_msg_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_622_);
lean_dec(v_a_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_628_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_633_, v_x_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec_ref(v_x_634_);
lean_dec_ref(v_x_633_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_641_, lean_object* v_expected_642_, lean_object* v_trailingFn_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_box_uint32(v_c_641_);
v___x_645_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_645_, 0, v___x_644_);
lean_closure_set(v___x_645_, 1, v_expected_642_);
v___x_646_ = l_Lake_Toml_atom(v___x_645_, v_trailingFn_643_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_647_, lean_object* v_expected_648_, lean_object* v_trailingFn_649_){
_start:
{
uint32_t v_c_boxed_650_; lean_object* v_res_651_; 
v_c_boxed_650_ = lean_unbox_uint32(v_c_647_);
lean_dec(v_c_647_);
v_res_651_ = l_Lake_Toml_chAtom(v_c_boxed_650_, v_expected_648_, v_trailingFn_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
uint8_t v___x_658_; lean_object* v___x_659_; 
v___x_658_ = 0;
v___x_659_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_652_, v___x_658_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
uint32_t v_c_boxed_666_; lean_object* v_res_667_; 
v_c_boxed_666_ = lean_unbox_uint32(v_c_660_);
lean_dec(v_c_660_);
v_res_667_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_666_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_668_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
uint32_t v_c_boxed_685_; lean_object* v_res_686_; 
v_c_boxed_685_ = lean_unbox_uint32(v_c_677_);
lean_dec(v_c_677_);
v_res_686_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_685_, v_x_678_, v_x_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec_ref(v_x_679_);
lean_dec(v_x_678_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_690_);
lean_dec(v_a_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
uint32_t v_x_18__boxed_710_; lean_object* v_res_711_; 
v_x_18__boxed_710_ = lean_unbox_uint32(v_x_702_);
lean_dec(v_x_702_);
v_res_711_ = l_Lake_Toml_chAtom_parenthesizer(v_x_18__boxed_710_, v_x_703_, v_x_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_x_704_);
lean_dec(v_x_703_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_712_, lean_object* v_expected_713_, lean_object* v_trailingFn_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_str_719_; lean_object* v_startInclusive_720_; lean_object* v_endExclusive_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_string_utf8_byte_size(v_s_712_);
v___x_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_717_, 0, v_s_712_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
v___x_718_ = l_String_Slice_trimAscii(v___x_717_);
v_str_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_str_719_);
v_startInclusive_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_startInclusive_720_);
v_endExclusive_721_ = lean_ctor_get(v___x_718_, 2);
lean_inc(v_endExclusive_721_);
lean_dec_ref(v___x_718_);
v___x_722_ = lean_string_utf8_extract(v_str_719_, v_startInclusive_720_, v_endExclusive_721_);
lean_dec(v_endExclusive_721_);
lean_dec(v_startInclusive_720_);
lean_dec_ref(v_str_719_);
v___x_723_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_723_, 0, v___x_722_);
lean_closure_set(v___x_723_, 1, v_expected_713_);
v___x_724_ = l_Lake_Toml_atom(v___x_723_, v_trailingFn_714_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_739_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lake_Toml_strAtom_formatter(v_s_748_, v_x_749_, v_x_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_x_750_);
lean_dec(v_x_749_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_760_);
lean_dec(v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_767_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lake_Toml_strAtom_parenthesizer(v_x_772_, v_x_773_, v_x_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_x_774_);
lean_dec(v_x_773_);
lean_dec_ref(v_x_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_781_, lean_object* v_startPos_782_, lean_object* v_trailingFn_783_, lean_object* v_c_784_, lean_object* v_s_785_){
_start:
{
lean_object* v_toInputContext_786_; lean_object* v_pos_787_; lean_object* v_inputString_788_; lean_object* v_endPos_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_807_; 
v_toInputContext_786_ = lean_ctor_get(v_c_784_, 0);
lean_inc_ref(v_toInputContext_786_);
v_pos_787_ = lean_ctor_get(v_s_785_, 2);
lean_inc(v_pos_787_);
v_inputString_788_ = lean_ctor_get(v_toInputContext_786_, 0);
v_endPos_789_ = lean_ctor_get(v_toInputContext_786_, 3);
v_isSharedCheck_807_ = !lean_is_exclusive(v_toInputContext_786_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; lean_object* v_unused_809_; 
v_unused_808_ = lean_ctor_get(v_toInputContext_786_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_toInputContext_786_, 1);
lean_dec(v_unused_809_);
v___x_791_ = v_toInputContext_786_;
v_isShared_792_ = v_isSharedCheck_807_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_endPos_789_);
lean_inc(v_inputString_788_);
lean_dec(v_toInputContext_786_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_807_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_leading_793_; lean_object* v_s_794_; lean_object* v_pos_795_; lean_object* v_val_796_; lean_object* v___y_798_; uint8_t v___x_804_; 
lean_inc(v_startPos_782_);
v_leading_793_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_784_, v_startPos_782_);
v_s_794_ = lean_apply_2(v_trailingFn_783_, v_c_784_, v_s_785_);
v_pos_795_ = lean_ctor_get(v_s_794_, 2);
lean_inc(v_pos_795_);
v_val_796_ = lean_string_utf8_extract(v_inputString_788_, v_startPos_782_, v_pos_787_);
v___x_804_ = lean_nat_dec_le(v_pos_795_, v_endPos_789_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec(v_pos_795_);
lean_inc(v_pos_787_);
v___x_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_805_, 0, v_inputString_788_);
lean_ctor_set(v___x_805_, 1, v_pos_787_);
lean_ctor_set(v___x_805_, 2, v_endPos_789_);
v___y_798_ = v___x_805_;
goto v___jp_797_;
}
else
{
lean_object* v___x_806_; 
lean_dec(v_endPos_789_);
lean_inc(v_pos_787_);
v___x_806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_806_, 0, v_inputString_788_);
lean_ctor_set(v___x_806_, 1, v_pos_787_);
lean_ctor_set(v___x_806_, 2, v_pos_795_);
v___y_798_ = v___x_806_;
goto v___jp_797_;
}
v___jp_797_:
{
lean_object* v_info_800_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 3, v_pos_787_);
lean_ctor_set(v___x_791_, 2, v___y_798_);
lean_ctor_set(v___x_791_, 1, v_startPos_782_);
lean_ctor_set(v___x_791_, 0, v_leading_793_);
v_info_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_leading_793_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_startPos_782_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v___y_798_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_pos_787_);
v_info_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Lean_Syntax_mkLit(v_kind_781_, v_val_796_, v_info_800_);
v___x_802_ = l_Lean_Parser_ParserState_pushSyntax(v_s_794_, v___x_801_);
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_810_, lean_object* v_p_811_, lean_object* v_trailingFn_812_, lean_object* v_c_813_, lean_object* v_s_814_){
_start:
{
lean_object* v_pos_815_; lean_object* v_s_816_; lean_object* v_errorMsg_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_pos_815_ = lean_ctor_get(v_s_814_, 2);
lean_inc(v_pos_815_);
lean_inc_ref(v_c_813_);
v_s_816_ = lean_apply_2(v_p_811_, v_c_813_, v_s_814_);
v_errorMsg_817_ = lean_ctor_get(v_s_816_, 4);
lean_inc(v_errorMsg_817_);
v___x_818_ = lean_box(0);
v___x_819_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_dec(v_pos_815_);
lean_dec_ref(v_c_813_);
lean_dec_ref(v_trailingFn_812_);
lean_dec(v_kind_810_);
return v_s_816_;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = l_Lake_Toml_pushLit(v_kind_810_, v_pos_815_, v_trailingFn_812_, v_c_813_, v_s_816_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_821_, lean_object* v_p_822_, lean_object* v_trailingFn_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_825_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_825_, 0, v_kind_821_);
lean_closure_set(v___x_825_, 1, v_p_822_);
lean_closure_set(v___x_825_, 2, v_trailingFn_823_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_Toml_lit_formatter___redArg(v_kind_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_841_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lake_Toml_lit_formatter(v_kind_850_, v_x_851_, v_x_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec_ref(v_x_852_);
lean_dec_ref(v_x_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_862_);
lean_dec(v_a_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_869_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lake_Toml_lit_parenthesizer(v_x_874_, v_x_875_, v_x_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec_ref(v_x_876_);
lean_dec_ref(v_x_875_);
lean_dec(v_x_874_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_897_, lean_object* v_kind_898_, uint8_t v_anonymous_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___f_905_; uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc(v_kind_898_);
v___f_905_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_905_, 0, v_kind_898_);
v___x_906_ = 0;
v___x_907_ = lean_box(v_anonymous_899_);
v___x_908_ = lean_box(v___x_906_);
v___x_909_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_909_, 0, v_name_897_);
lean_closure_set(v___x_909_, 1, v_kind_898_);
lean_closure_set(v___x_909_, 2, v___x_907_);
lean_closure_set(v___x_909_, 3, v___x_908_);
v___x_910_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_909_, v___f_905_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_911_, lean_object* v_kind_912_, lean_object* v_anonymous_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
uint8_t v_anonymous_boxed_919_; lean_object* v_res_920_; 
v_anonymous_boxed_919_ = lean_unbox(v_anonymous_913_);
v_res_920_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_911_, v_kind_912_, v_anonymous_boxed_919_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_921_, lean_object* v_kind_922_, lean_object* v_p_923_, lean_object* v_trailingFn_924_, uint8_t v_anonymous_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_921_, v_kind_922_, v_anonymous_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_932_, lean_object* v_kind_933_, lean_object* v_p_934_, lean_object* v_trailingFn_935_, lean_object* v_anonymous_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
uint8_t v_anonymous_boxed_942_; lean_object* v_res_943_; 
v_anonymous_boxed_942_ = lean_unbox(v_anonymous_936_);
v_res_943_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_932_, v_kind_933_, v_p_934_, v_trailingFn_935_, v_anonymous_boxed_942_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec_ref(v_trailingFn_935_);
lean_dec_ref(v_p_934_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_945_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_957_, lean_object* v_kind_958_, uint8_t v_anonymous_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___f_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___f_965_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_966_ = 0;
v___x_967_ = lean_box(v_anonymous_959_);
v___x_968_ = lean_box(v___x_966_);
v___x_969_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_969_, 0, v_name_957_);
lean_closure_set(v___x_969_, 1, v_kind_958_);
lean_closure_set(v___x_969_, 2, v___x_967_);
lean_closure_set(v___x_969_, 3, v___x_968_);
v___x_970_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_969_, v___f_965_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_971_, lean_object* v_kind_972_, lean_object* v_anonymous_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_anonymous_boxed_979_; lean_object* v_res_980_; 
v_anonymous_boxed_979_ = lean_unbox(v_anonymous_973_);
v_res_980_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_971_, v_kind_972_, v_anonymous_boxed_979_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_981_, lean_object* v_kind_982_, lean_object* v_p_983_, lean_object* v_trailingFn_984_, uint8_t v_anonymous_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_981_, v_kind_982_, v_anonymous_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_992_, lean_object* v_kind_993_, lean_object* v_p_994_, lean_object* v_trailingFn_995_, lean_object* v_anonymous_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
uint8_t v_anonymous_boxed_1002_; lean_object* v_res_1003_; 
v_anonymous_boxed_1002_ = lean_unbox(v_anonymous_996_);
v_res_1003_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_992_, v_kind_993_, v_p_994_, v_trailingFn_995_, v_anonymous_boxed_1002_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec_ref(v_trailingFn_995_);
lean_dec_ref(v_p_994_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1004_, lean_object* v_kind_1005_, lean_object* v_p_1006_, lean_object* v_trailingFn_1007_, uint8_t v_anonymous_1008_){
_start:
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1009_ = 0;
lean_inc(v_kind_1005_);
v___x_1010_ = l_Lean_Parser_mkAntiquot(v_name_1004_, v_kind_1005_, v_anonymous_1008_, v___x_1009_);
v___x_1011_ = l_Lake_Toml_lit(v_kind_1005_, v_p_1006_, v_trailingFn_1007_);
v___x_1012_ = l_Lean_Parser_withAntiquot(v___x_1010_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1013_, lean_object* v_kind_1014_, lean_object* v_p_1015_, lean_object* v_trailingFn_1016_, lean_object* v_anonymous_1017_){
_start:
{
uint8_t v_anonymous_boxed_1018_; lean_object* v_res_1019_; 
v_anonymous_boxed_1018_ = lean_unbox(v_anonymous_1017_);
v_res_1019_ = l_Lake_Toml_litWithAntiquot(v_name_1013_, v_kind_1014_, v_p_1015_, v_trailingFn_1016_, v_anonymous_boxed_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = l_Lean_Parser_epsilonInfo;
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v_fn_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lake_Toml_epsilon_formatter(v_x_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec_ref(v_x_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec_ref(v_x_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1061_, lean_object* v_x_1062_){
_start:
{
switch(lean_obj_tag(v_x_1062_))
{
case 2:
{
lean_object* v_info_1063_; lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_info_1063_ = lean_ctor_get(v_x_1062_, 0);
v_val_1064_ = lean_ctor_get(v_x_1062_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1066_ = v_x_1062_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_inc(v_info_1063_);
lean_dec(v_x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_apply_1(v_f_1061_, v_info_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_val_1064_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
case 3:
{
lean_object* v_info_1073_; lean_object* v_rawVal_1074_; lean_object* v_val_1075_; lean_object* v_preresolved_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_info_1073_ = lean_ctor_get(v_x_1062_, 0);
v_rawVal_1074_ = lean_ctor_get(v_x_1062_, 1);
v_val_1075_ = lean_ctor_get(v_x_1062_, 2);
v_preresolved_1076_ = lean_ctor_get(v_x_1062_, 3);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_x_1062_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_preresolved_1076_);
lean_inc(v_val_1075_);
lean_inc(v_rawVal_1074_);
lean_inc(v_info_1073_);
lean_dec(v_x_1062_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_apply_1(v_f_1061_, v_info_1073_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_rawVal_1074_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_val_1075_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_preresolved_1076_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
case 1:
{
lean_object* v_info_1085_; lean_object* v_kind_1086_; lean_object* v_args_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_info_1085_ = lean_ctor_get(v_x_1062_, 0);
v_kind_1086_ = lean_ctor_get(v_x_1062_, 1);
v_args_1087_ = lean_ctor_get(v_x_1062_, 2);
v___x_1088_ = lean_array_get_size(v_args_1087_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_sub(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_nat_dec_lt(v___x_1090_, v___x_1088_);
if (v___x_1091_ == 0)
{
lean_dec(v___x_1090_);
lean_dec_ref(v_f_1061_);
return v_x_1062_;
}
else
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1103_; 
lean_inc_ref(v_args_1087_);
lean_inc(v_kind_1086_);
lean_inc(v_info_1085_);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; 
v_unused_1104_ = lean_ctor_get(v_x_1062_, 2);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_x_1062_, 1);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_x_1062_, 0);
lean_dec(v_unused_1106_);
v___x_1093_ = v_x_1062_;
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v_x_1062_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_v_1095_; lean_object* v___x_1096_; lean_object* v_xs_x27_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v_v_1095_ = lean_array_fget(v_args_1087_, v___x_1090_);
v___x_1096_ = lean_box(0);
v_xs_x27_1097_ = lean_array_fset(v_args_1087_, v___x_1090_, v___x_1096_);
v___x_1098_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1061_, v_v_1095_);
v___x_1099_ = lean_array_fset(v_xs_x27_1097_, v___x_1090_, v___x_1098_);
lean_dec(v___x_1090_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 2, v___x_1099_);
v___x_1101_ = v___x_1093_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_info_1085_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_kind_1086_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1061_);
return v_x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1107_, lean_object* v_x_1108_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v_trailing_1109_; lean_object* v_leading_1110_; lean_object* v_pos_1111_; lean_object* v_endPos_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1129_; 
v_trailing_1109_ = lean_ctor_get(v_x_1108_, 2);
v_leading_1110_ = lean_ctor_get(v_x_1108_, 0);
v_pos_1111_ = lean_ctor_get(v_x_1108_, 1);
v_endPos_1112_ = lean_ctor_get(v_x_1108_, 3);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1114_ = v_x_1108_;
v_isShared_1115_ = v_isSharedCheck_1129_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_endPos_1112_);
lean_inc(v_trailing_1109_);
lean_inc(v_pos_1111_);
lean_inc(v_leading_1110_);
lean_dec(v_x_1108_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1129_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_str_1116_; lean_object* v_startPos_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1127_; 
v_str_1116_ = lean_ctor_get(v_trailing_1109_, 0);
v_startPos_1117_ = lean_ctor_get(v_trailing_1109_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_trailing_1109_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_trailing_1109_, 2);
lean_dec(v_unused_1128_);
v___x_1119_ = v_trailing_1109_;
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_startPos_1117_);
lean_inc(v_str_1116_);
lean_dec(v_trailing_1109_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 2, v_stopPos_1107_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_str_1116_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_startPos_1117_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_stopPos_1107_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 2, v___x_1122_);
v___x_1124_ = v___x_1114_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_leading_1110_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_pos_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_endPos_1112_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
else
{
lean_dec(v_stopPos_1107_);
return v_x_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1130_, lean_object* v_x_1131_){
_start:
{
switch(lean_obj_tag(v_x_1131_))
{
case 2:
{
lean_object* v_info_1132_; lean_object* v_val_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_info_1132_ = lean_ctor_get(v_x_1131_, 0);
v_val_1133_ = lean_ctor_get(v_x_1131_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v_x_1131_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_val_1133_);
lean_inc(v_info_1132_);
lean_dec(v_x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1130_, v_info_1132_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_val_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
case 3:
{
lean_object* v_info_1142_; lean_object* v_rawVal_1143_; lean_object* v_val_1144_; lean_object* v_preresolved_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v_info_1142_ = lean_ctor_get(v_x_1131_, 0);
v_rawVal_1143_ = lean_ctor_get(v_x_1131_, 1);
v_val_1144_ = lean_ctor_get(v_x_1131_, 2);
v_preresolved_1145_ = lean_ctor_get(v_x_1131_, 3);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v_x_1131_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_preresolved_1145_);
lean_inc(v_val_1144_);
lean_inc(v_rawVal_1143_);
lean_inc(v_info_1142_);
lean_dec(v_x_1131_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1130_, v_info_1142_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_rawVal_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_val_1144_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_preresolved_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
case 1:
{
lean_object* v_info_1154_; lean_object* v_kind_1155_; lean_object* v_args_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_info_1154_ = lean_ctor_get(v_x_1131_, 0);
v_kind_1155_ = lean_ctor_get(v_x_1131_, 1);
v_args_1156_ = lean_ctor_get(v_x_1131_, 2);
v___x_1157_ = lean_array_get_size(v_args_1156_);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_sub(v___x_1157_, v___x_1158_);
v___x_1160_ = lean_nat_dec_lt(v___x_1159_, v___x_1157_);
if (v___x_1160_ == 0)
{
lean_dec(v___x_1159_);
lean_dec(v_stopPos_1130_);
return v_x_1131_;
}
else
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1172_; 
lean_inc_ref(v_args_1156_);
lean_inc(v_kind_1155_);
lean_inc(v_info_1154_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1173_ = lean_ctor_get(v_x_1131_, 2);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_x_1131_, 1);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_x_1131_, 0);
lean_dec(v_unused_1175_);
v___x_1162_ = v_x_1131_;
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v_x_1131_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_v_1164_; lean_object* v___x_1165_; lean_object* v_xs_x27_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v_v_1164_ = lean_array_fget(v_args_1156_, v___x_1159_);
v___x_1165_ = lean_box(0);
v_xs_x27_1166_ = lean_array_fset(v_args_1156_, v___x_1159_, v___x_1165_);
v___x_1167_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1130_, v_v_1164_);
v___x_1168_ = lean_array_fset(v_xs_x27_1166_, v___x_1159_, v___x_1167_);
lean_dec(v___x_1159_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 2, v___x_1168_);
v___x_1170_ = v___x_1162_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_info_1154_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_kind_1155_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1130_);
return v_x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1176_, lean_object* v_c_1177_, lean_object* v_s_1178_){
_start:
{
lean_object* v_s_1179_; lean_object* v_stxStack_1180_; lean_object* v_pos_1181_; lean_object* v_tail_1182_; lean_object* v_s_1183_; lean_object* v_tail_1184_; lean_object* v___x_1185_; 
v_s_1179_ = lean_apply_2(v_p_1176_, v_c_1177_, v_s_1178_);
v_stxStack_1180_ = lean_ctor_get(v_s_1179_, 0);
lean_inc_ref(v_stxStack_1180_);
v_pos_1181_ = lean_ctor_get(v_s_1179_, 2);
lean_inc(v_pos_1181_);
v_tail_1182_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1180_);
lean_dec_ref(v_stxStack_1180_);
v_s_1183_ = l_Lean_Parser_ParserState_popSyntax(v_s_1179_);
v_tail_1184_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1181_, v_tail_1182_);
v___x_1185_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1183_, v_tail_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lake_Toml_trailing_formatter(v_p_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec_ref(v_p_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lake_Toml_trailing_parenthesizer(v_p_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec_ref(v_p_1215_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1223_, 0, v_p_1222_);
v___x_1224_ = l_Lean_Parser_epsilonInfo;
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v_p_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1234_; lean_object* v_a_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1230_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = l_Lean_Syntax_getKind(v_a_1235_);
v___x_1237_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1236_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lake_Toml_dynamicNode_formatter(v_x_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec_ref(v_x_1251_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_stxTrav_1261_; lean_object* v_cur_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_st_ref_get(v___y_1258_);
v_stxTrav_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_stxTrav_1261_);
lean_dec(v___x_1260_);
v_cur_1262_ = lean_ctor_get(v_stxTrav_1261_, 0);
lean_inc(v_cur_1262_);
lean_dec_ref(v_stxTrav_1261_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_cur_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1264_);
lean_dec(v___y_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1268_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1280_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = l_Lean_Syntax_getKind(v_a_1285_);
v___x_1287_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1286_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec_ref(v_x_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_fn_1314_; lean_object* v___x_1315_; 
lean_inc_ref(v_f_1308_);
v___x_1311_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1311_, 0, v_f_1308_);
v___x_1312_ = l_Lake_Toml_dynamicNode(v___x_1311_);
v___x_1313_ = lean_apply_1(v_f_1308_, v___x_1312_);
v_fn_1314_ = lean_ctor_get(v___x_1313_, 1);
lean_inc_ref(v_fn_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_apply_2(v_fn_1314_, v_a_1309_, v_a_1310_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lake_Toml_recNode_formatter(v_f_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec_ref(v_f_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lake_Toml_recNode_parenthesizer(v_f_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec_ref(v_f_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1369_, 0, v_f_1368_);
v___x_1370_ = l_Lake_Toml_dynamicNode(v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1371_, lean_object* v_kind_1372_, lean_object* v_f_1373_, uint8_t v_anonymous_1374_, lean_object* v_p_1375_){
_start:
{
uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1376_ = 1;
lean_inc(v_kind_1372_);
v___x_1377_ = l_Lean_Parser_mkAntiquot(v_name_1371_, v_kind_1372_, v_anonymous_1374_, v___x_1376_);
v___x_1378_ = lean_apply_1(v_f_1373_, v_p_1375_);
v___x_1379_ = l_Lean_Parser_withAntiquot(v___x_1377_, v___x_1378_);
v___x_1380_ = l_Lean_Parser_withCache(v_kind_1372_, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1381_, lean_object* v_kind_1382_, lean_object* v_f_1383_, lean_object* v_anonymous_1384_, lean_object* v_p_1385_){
_start:
{
uint8_t v_anonymous_boxed_1386_; lean_object* v_res_1387_; 
v_anonymous_boxed_1386_ = lean_unbox(v_anonymous_1384_);
v_res_1387_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1381_, v_kind_1382_, v_f_1383_, v_anonymous_boxed_1386_, v_p_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1388_, lean_object* v_kind_1389_, lean_object* v_f_1390_, uint8_t v_anonymous_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1397_ = 1;
v___x_1398_ = lean_box(v_anonymous_1391_);
v___x_1399_ = lean_box(v___x_1397_);
lean_inc(v_kind_1389_);
lean_inc_ref(v_name_1388_);
v___x_1400_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1400_, 0, v_name_1388_);
lean_closure_set(v___x_1400_, 1, v_kind_1389_);
lean_closure_set(v___x_1400_, 2, v___x_1398_);
lean_closure_set(v___x_1400_, 3, v___x_1399_);
v___x_1401_ = lean_box(v_anonymous_1391_);
v___x_1402_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1402_, 0, v_name_1388_);
lean_closure_set(v___x_1402_, 1, v_kind_1389_);
lean_closure_set(v___x_1402_, 2, v_f_1390_);
lean_closure_set(v___x_1402_, 3, v___x_1401_);
v___x_1403_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1403_, 0, v___x_1402_);
v___x_1404_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1400_, v___x_1403_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1405_, lean_object* v_kind_1406_, lean_object* v_f_1407_, lean_object* v_anonymous_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
uint8_t v_anonymous_boxed_1414_; lean_object* v_res_1415_; 
v_anonymous_boxed_1414_ = lean_unbox(v_anonymous_1408_);
v_res_1415_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1405_, v_kind_1406_, v_f_1407_, v_anonymous_boxed_1414_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1416_, lean_object* v_kind_1417_, lean_object* v_f_1418_, uint8_t v_anonymous_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1425_ = 1;
v___x_1426_ = lean_box(v_anonymous_1419_);
v___x_1427_ = lean_box(v___x_1425_);
lean_inc(v_kind_1417_);
lean_inc_ref(v_name_1416_);
v___x_1428_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1428_, 0, v_name_1416_);
lean_closure_set(v___x_1428_, 1, v_kind_1417_);
lean_closure_set(v___x_1428_, 2, v___x_1426_);
lean_closure_set(v___x_1428_, 3, v___x_1427_);
v___x_1429_ = lean_box(v_anonymous_1419_);
v___x_1430_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1430_, 0, v_name_1416_);
lean_closure_set(v___x_1430_, 1, v_kind_1417_);
lean_closure_set(v___x_1430_, 2, v_f_1418_);
lean_closure_set(v___x_1430_, 3, v___x_1429_);
v___x_1431_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1431_, 0, v___x_1430_);
v___x_1432_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1428_, v___x_1431_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1433_, lean_object* v_kind_1434_, lean_object* v_f_1435_, lean_object* v_anonymous_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
uint8_t v_anonymous_boxed_1442_; lean_object* v_res_1443_; 
v_anonymous_boxed_1442_ = lean_unbox(v_anonymous_1436_);
v_res_1443_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1433_, v_kind_1434_, v_f_1435_, v_anonymous_boxed_1442_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1444_, lean_object* v_kind_1445_, lean_object* v_f_1446_, uint8_t v_anonymous_1447_){
_start:
{
uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1448_ = 1;
lean_inc_n(v_kind_1445_, 2);
lean_inc_ref(v_name_1444_);
v___x_1449_ = l_Lean_Parser_mkAntiquot(v_name_1444_, v_kind_1445_, v_anonymous_1447_, v___x_1448_);
v___x_1450_ = lean_box(v_anonymous_1447_);
v___x_1451_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1451_, 0, v_name_1444_);
lean_closure_set(v___x_1451_, 1, v_kind_1445_);
lean_closure_set(v___x_1451_, 2, v_f_1446_);
lean_closure_set(v___x_1451_, 3, v___x_1450_);
v___x_1452_ = l_Lake_Toml_recNode(v___x_1451_);
v___x_1453_ = l_Lean_Parser_withAntiquot(v___x_1449_, v___x_1452_);
v___x_1454_ = l_Lean_Parser_withCache(v_kind_1445_, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1455_, lean_object* v_kind_1456_, lean_object* v_f_1457_, lean_object* v_anonymous_1458_){
_start:
{
uint8_t v_anonymous_boxed_1459_; lean_object* v_res_1460_; 
v_anonymous_boxed_1459_ = lean_unbox(v_anonymous_1458_);
v_res_1460_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1455_, v_kind_1456_, v_f_1457_, v_anonymous_boxed_1459_);
return v_res_1460_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___f_1468_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1469_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1470_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1470_, 0, v___x_1469_);
lean_closure_set(v___x_1470_, 1, v___f_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1477_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1478_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1479_, 0, v___x_1477_);
lean_closure_set(v___x_1479_, 1, v_p_1471_);
lean_closure_set(v___x_1479_, 2, v___x_1478_);
v___x_1480_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1481_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1479_, v___x_1480_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1489_, uint8_t v_allowTrailingLinebreak_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1489_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1497_, lean_object* v_allowTrailingLinebreak_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1504_; lean_object* v_res_1505_; 
v_allowTrailingLinebreak_boxed_1504_ = lean_unbox(v_allowTrailingLinebreak_1498_);
v_res_1505_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1497_, v_allowTrailingLinebreak_boxed_1504_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1505_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___f_1509_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1510_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1511_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1511_, 0, v___x_1510_);
lean_closure_set(v___x_1511_, 1, v___f_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1518_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1519_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1520_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1520_, 0, v___x_1518_);
lean_closure_set(v___x_1520_, 1, v_p_1512_);
lean_closure_set(v___x_1520_, 2, v___x_1519_);
v___x_1521_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1522_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1520_, v___x_1521_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1530_, uint8_t v_allowTrailingLinebreak_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1530_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1538_, lean_object* v_allowTrailingLinebreak_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1545_; lean_object* v_res_1546_; 
v_allowTrailingLinebreak_boxed_1545_ = lean_unbox(v_allowTrailingLinebreak_1539_);
v_res_1546_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1538_, v_allowTrailingLinebreak_boxed_1545_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1548_ = l_Lean_Parser_symbol(v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1551_ = l_Lean_Parser_checkLinebreakBefore(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = l_Lean_Parser_pushNone;
v___x_1553_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1554_ = l_Lean_Parser_andthen(v___x_1553_, v___x_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1555_, uint8_t v_allowTrailingLinebreak_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_p_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1557_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1558_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1559_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1557_, v_p_1555_, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1561_ = l_Lean_Parser_sepByNoAntiquot(v_p_1559_, v___x_1560_, v_allowTrailingLinebreak_1556_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1562_, lean_object* v_allowTrailingLinebreak_1563_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1564_; lean_object* v_res_1565_; 
v_allowTrailingLinebreak_boxed_1564_ = lean_unbox(v_allowTrailingLinebreak_1563_);
v_res_1565_ = l_Lake_Toml_sepByLinebreak(v_p_1562_, v_allowTrailingLinebreak_boxed_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1572_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1573_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1574_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1574_, 0, v___x_1572_);
lean_closure_set(v___x_1574_, 1, v_p_1566_);
lean_closure_set(v___x_1574_, 2, v___x_1573_);
v___x_1575_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1576_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1574_, v___x_1575_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1584_, uint8_t v_allowTrailingLinebreak_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1584_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1592_, lean_object* v_allowTrailingLinebreak_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1599_; lean_object* v_res_1600_; 
v_allowTrailingLinebreak_boxed_1599_ = lean_unbox(v_allowTrailingLinebreak_1593_);
v_res_1600_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1592_, v_allowTrailingLinebreak_boxed_1599_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1607_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1608_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1609_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1609_, 0, v___x_1607_);
lean_closure_set(v___x_1609_, 1, v_p_1601_);
lean_closure_set(v___x_1609_, 2, v___x_1608_);
v___x_1610_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1611_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1609_, v___x_1610_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1619_, uint8_t v_allowTrailingLinebreak_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1619_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1627_, lean_object* v_allowTrailingLinebreak_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1634_; lean_object* v_res_1635_; 
v_allowTrailingLinebreak_boxed_1634_ = lean_unbox(v_allowTrailingLinebreak_1628_);
v_res_1635_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1627_, v_allowTrailingLinebreak_boxed_1634_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1636_, uint8_t v_allowTrailingLinebreak_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_p_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1638_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1639_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1640_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1638_, v_p_1636_, v___x_1639_);
v___x_1641_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1642_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1640_, v___x_1641_, v_allowTrailingLinebreak_1637_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1643_, lean_object* v_allowTrailingLinebreak_1644_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1645_; lean_object* v_res_1646_; 
v_allowTrailingLinebreak_boxed_1645_ = lean_unbox(v_allowTrailingLinebreak_1644_);
v_res_1646_ = l_Lake_Toml_sepBy1Linebreak(v_p_1643_, v_allowTrailingLinebreak_boxed_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1647_, lean_object* v_c_1648_, lean_object* v_s_1649_){
_start:
{
lean_object* v_toCacheableParserContext_1650_; lean_object* v_quotDepth_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_toCacheableParserContext_1650_ = lean_ctor_get(v_c_1648_, 2);
v_quotDepth_1651_ = lean_ctor_get(v_toCacheableParserContext_1650_, 1);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_nat_dec_lt(v___x_1652_, v_quotDepth_1651_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_apply_2(v_p_1647_, v_c_1648_, v_s_1649_);
return v___x_1654_;
}
else
{
lean_dec_ref(v_c_1648_);
lean_dec_ref(v_p_1647_);
return v_s_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; 
lean_inc(v_a_1659_);
lean_inc_ref(v_a_1658_);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
v___x_1661_ = lean_apply_5(v_p_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, lean_box(0));
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1675_; 
lean_inc(v_a_1673_);
lean_inc_ref(v_a_1672_);
lean_inc(v_a_1671_);
lean_inc_ref(v_a_1670_);
v___x_1675_ = lean_apply_5(v_p_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, lean_box(0));
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1683_){
_start:
{
lean_object* v_info_1684_; lean_object* v_fn_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
v_info_1684_ = lean_ctor_get(v_p_1683_, 0);
v_fn_1685_ = lean_ctor_get(v_p_1683_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_p_1683_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1687_ = v_p_1683_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_fn_1685_);
lean_inc(v_info_1684_);
lean_dec(v_p_1683_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1689_, 0, v_fn_1685_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 1, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_info_1684_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
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
