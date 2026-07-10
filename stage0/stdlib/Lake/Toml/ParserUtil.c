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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_s_53_; lean_object* v_errorMsg_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; uint8_t v___x_58_; 
lean_inc_ref(v_c_51_);
v_s_53_ = lean_apply_2(v_p_49_, v_c_51_, v_s_52_);
v_errorMsg_54_ = lean_ctor_get(v_s_53_, 4);
lean_inc(v_errorMsg_54_);
v___x_55_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_56_ = lean_box(0);
v___x_57_ = l_Option_instBEq_beq___redArg(v___x_55_, v_errorMsg_54_, v___x_56_);
v___x_58_ = lean_bool_not(v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_3(v_q_50_, v___x_59_, v_c_51_, v_s_53_);
return v___x_60_;
}
else
{
lean_dec_ref(v_c_51_);
lean_dec_ref(v_q_50_);
return v_s_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_usePosFn(lean_object* v_f_63_, lean_object* v_c_64_, lean_object* v_s_65_){
_start:
{
lean_object* v_pos_66_; lean_object* v___x_67_; 
v_pos_66_ = lean_ctor_get(v_s_65_, 2);
lean_inc(v_pos_66_);
v___x_67_ = lean_apply_3(v_f_63_, v_pos_66_, v_c_64_, v_s_65_);
return v___x_67_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
lean_dec_ref_known(v_x_69_, 1);
v___x_71_ = 0;
return v___x_71_;
}
}
else
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_72_; 
lean_dec_ref_known(v_x_68_, 1);
v___x_72_ = 0;
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v_val_74_; uint8_t v___x_75_; 
v_val_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v_x_68_, 1);
v_val_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v_x_69_, 1);
v___x_75_ = l_Lean_Parser_instBEqError_beq(v_val_73_, v_val_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_x_76_, v_x_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object* v_p_80_, lean_object* v_c_81_, lean_object* v_s_82_){
_start:
{
lean_object* v_pos_83_; lean_object* v_iniSz_84_; lean_object* v_s_85_; uint8_t v___y_87_; lean_object* v_pos_89_; lean_object* v_errorMsg_90_; lean_object* v___x_91_; uint8_t v___x_92_; uint8_t v___x_93_; 
v_pos_83_ = lean_ctor_get(v_s_82_, 2);
lean_inc(v_pos_83_);
v_iniSz_84_ = l_Lean_Parser_ParserState_stackSize(v_s_82_);
v_s_85_ = lean_apply_2(v_p_80_, v_c_81_, v_s_82_);
v_pos_89_ = lean_ctor_get(v_s_85_, 2);
lean_inc(v_pos_89_);
v_errorMsg_90_ = lean_ctor_get(v_s_85_, 4);
lean_inc(v_errorMsg_90_);
v___x_91_ = lean_box(0);
v___x_92_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_90_, v___x_91_);
v___x_93_ = lean_bool_not(v___x_92_);
if (v___x_93_ == 0)
{
lean_dec(v_pos_89_);
v___y_87_ = v___x_93_;
goto v___jp_86_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_eq(v_pos_89_, v_pos_83_);
lean_dec(v_pos_89_);
v___y_87_ = v___x_94_;
goto v___jp_86_;
}
v___jp_86_:
{
if (v___y_87_ == 0)
{
lean_dec(v_iniSz_84_);
lean_dec(v_pos_83_);
return v_s_85_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Parser_ParserState_restore(v_s_85_, v_iniSz_84_, v_pos_83_);
lean_dec(v_iniSz_84_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object* v_p_95_, lean_object* v_c_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
lean_object* v_zero_99_; uint8_t v_isZero_100_; 
v_zero_99_ = lean_unsigned_to_nat(0u);
v_isZero_100_ = lean_nat_dec_eq(v_x_97_, v_zero_99_);
if (v_isZero_100_ == 1)
{
lean_dec(v_x_97_);
lean_dec_ref(v_c_96_);
lean_dec_ref(v_p_95_);
return v_x_98_;
}
else
{
lean_object* v_s_101_; lean_object* v_errorMsg_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; 
lean_inc_ref(v_p_95_);
lean_inc_ref(v_c_96_);
v_s_101_ = lean_apply_2(v_p_95_, v_c_96_, v_x_98_);
v_errorMsg_102_ = lean_ctor_get(v_s_101_, 4);
lean_inc(v_errorMsg_102_);
v___x_103_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_104_ = lean_box(0);
v___x_105_ = l_Option_instBEq_beq___redArg(v___x_103_, v_errorMsg_102_, v___x_104_);
v___x_106_ = lean_bool_not(v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v_one_107_; lean_object* v_n_108_; 
v_one_107_ = lean_unsigned_to_nat(1u);
v_n_108_ = lean_nat_sub(v_x_97_, v_one_107_);
lean_dec(v_x_97_);
v_x_97_ = v_n_108_;
v_x_98_ = v_s_101_;
goto _start;
}
else
{
lean_dec(v_x_97_);
lean_dec_ref(v_c_96_);
lean_dec_ref(v_p_95_);
return v_s_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object* v_n_110_, lean_object* v_p_111_, lean_object* v_c_112_, lean_object* v_s_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(v_p_111_, v_c_112_, v_n_110_, v_s_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object* v_s_118_, uint32_t v_c_119_, lean_object* v_expected_120_, uint8_t v_pushMissing_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_122_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__0));
v___x_123_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_124_ = lean_string_push(v___x_123_, v_c_119_);
v___x_125_ = lean_string_append(v___x_122_, v___x_124_);
lean_dec_ref(v___x_124_);
v___x_126_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_118_, v___x_127_, v_expected_120_, v_pushMissing_121_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object* v_s_129_, lean_object* v_c_130_, lean_object* v_expected_131_, lean_object* v_pushMissing_132_){
_start:
{
uint32_t v_c_boxed_133_; uint8_t v_pushMissing_boxed_134_; lean_object* v_res_135_; 
v_c_boxed_133_ = lean_unbox_uint32(v_c_130_);
lean_dec(v_c_130_);
v_pushMissing_boxed_134_ = lean_unbox(v_pushMissing_132_);
v_res_135_ = l_Lake_Toml_mkUnexpectedCharError(v_s_129_, v_c_boxed_133_, v_expected_131_, v_pushMissing_boxed_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object* v_p_136_, lean_object* v_expected_137_, lean_object* v_c_138_, lean_object* v_s_139_){
_start:
{
lean_object* v_pos_140_; lean_object* v_toInputContext_141_; uint8_t v___x_142_; 
v_pos_140_ = lean_ctor_get(v_s_139_, 2);
v_toInputContext_141_ = lean_ctor_get(v_c_138_, 0);
v___x_142_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_141_, v_pos_140_);
if (v___x_142_ == 0)
{
lean_object* v_inputString_143_; uint32_t v_curr_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_inputString_143_ = lean_ctor_get(v_toInputContext_141_, 0);
v_curr_144_ = lean_string_utf8_get_fast(v_inputString_143_, v_pos_140_);
v___x_145_ = lean_box_uint32(v_curr_144_);
v___x_146_ = lean_apply_1(v_p_136_, v___x_145_);
v___x_147_ = lean_unbox(v___x_146_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; lean_object* v___x_149_; 
v___x_148_ = 1;
v___x_149_ = l_Lake_Toml_mkUnexpectedCharError(v_s_139_, v_curr_144_, v_expected_137_, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; 
lean_inc(v_pos_140_);
lean_dec(v_expected_137_);
v___x_150_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_139_, v_c_138_, v_pos_140_);
lean_dec(v_pos_140_);
return v___x_150_;
}
}
else
{
lean_object* v___x_151_; 
lean_dec_ref(v_p_136_);
v___x_151_ = l_Lean_Parser_ParserState_mkEOIError(v_s_139_, v_expected_137_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object* v_p_152_, lean_object* v_expected_153_, lean_object* v_c_154_, lean_object* v_s_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lake_Toml_satisfyFn(v_p_152_, v_expected_153_, v_c_154_, v_s_155_);
lean_dec_ref(v_c_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object* v_p_157_, lean_object* v_expected_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___y_162_; lean_object* v_pos_168_; lean_object* v_toInputContext_169_; uint8_t v___x_170_; 
v_pos_168_ = lean_ctor_get(v_a_160_, 2);
v_toInputContext_169_ = lean_ctor_get(v_a_159_, 0);
v___x_170_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_169_, v_pos_168_);
if (v___x_170_ == 0)
{
lean_object* v_inputString_171_; uint32_t v_curr_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_inputString_171_ = lean_ctor_get(v_toInputContext_169_, 0);
v_curr_172_ = lean_string_utf8_get_fast(v_inputString_171_, v_pos_168_);
v___x_173_ = lean_box_uint32(v_curr_172_);
lean_inc_ref(v_p_157_);
v___x_174_ = lean_apply_1(v_p_157_, v___x_173_);
v___x_175_ = lean_unbox(v___x_174_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; lean_object* v___x_177_; 
v___x_176_ = 1;
v___x_177_ = l_Lake_Toml_mkUnexpectedCharError(v_a_160_, v_curr_172_, v_expected_158_, v___x_176_);
v___y_162_ = v___x_177_;
goto v___jp_161_;
}
else
{
lean_object* v___x_178_; 
lean_inc(v_pos_168_);
lean_dec(v_expected_158_);
v___x_178_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_160_, v_a_159_, v_pos_168_);
lean_dec(v_pos_168_);
v___y_162_ = v___x_178_;
goto v___jp_161_;
}
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Parser_ParserState_mkEOIError(v_a_160_, v_expected_158_);
v___y_162_ = v___x_179_;
goto v___jp_161_;
}
v___jp_161_:
{
lean_object* v_errorMsg_163_; lean_object* v___x_164_; uint8_t v___x_165_; uint8_t v___x_166_; 
v_errorMsg_163_ = lean_ctor_get(v___y_162_, 4);
v___x_164_ = lean_box(0);
lean_inc(v_errorMsg_163_);
v___x_165_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_163_, v___x_164_);
v___x_166_ = lean_bool_not(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Parser_takeWhileFn(v_p_157_, v_a_159_, v___y_162_);
return v___x_167_;
}
else
{
lean_dec_ref(v_p_157_);
return v___y_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object* v_p_180_, lean_object* v_expected_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lake_Toml_takeWhile1Fn(v_p_180_, v_expected_181_, v_a_182_, v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object* v_expected_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_pos_188_; lean_object* v_toInputContext_189_; uint8_t v___x_190_; 
v_pos_188_ = lean_ctor_get(v_a_187_, 2);
v_toInputContext_189_ = lean_ctor_get(v_a_186_, 0);
v___x_190_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_189_, v_pos_188_);
if (v___x_190_ == 0)
{
lean_object* v_inputString_191_; uint32_t v_curr_192_; uint8_t v___y_194_; uint32_t v___x_198_; uint8_t v___x_199_; 
v_inputString_191_ = lean_ctor_get(v_toInputContext_189_, 0);
v_curr_192_ = lean_string_utf8_get_fast(v_inputString_191_, v_pos_188_);
v___x_198_ = 48;
v___x_199_ = lean_uint32_dec_le(v___x_198_, v_curr_192_);
if (v___x_199_ == 0)
{
v___y_194_ = v___x_199_;
goto v___jp_193_;
}
else
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 57;
v___x_201_ = lean_uint32_dec_le(v_curr_192_, v___x_200_);
v___y_194_ = v___x_201_;
goto v___jp_193_;
}
v___jp_193_:
{
if (v___y_194_ == 0)
{
uint8_t v___x_195_; lean_object* v___x_196_; 
v___x_195_ = 1;
v___x_196_ = l_Lake_Toml_mkUnexpectedCharError(v_a_187_, v_curr_192_, v_expected_185_, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
lean_inc(v_pos_188_);
lean_dec(v_expected_185_);
v___x_197_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_187_, v_a_186_, v_pos_188_);
lean_dec(v_pos_188_);
return v___x_197_;
}
}
}
else
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Parser_ParserState_mkEOIError(v_a_187_, v_expected_185_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object* v_expected_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_Toml_digitFn(v_expected_203_, v_a_204_, v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object* v_expected_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_s_210_; lean_object* v_errorMsg_211_; lean_object* v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; 
lean_inc(v_expected_207_);
v_s_210_ = l_Lake_Toml_digitFn(v_expected_207_, v_a_208_, v_a_209_);
v_errorMsg_211_ = lean_ctor_get(v_s_210_, 4);
lean_inc(v_errorMsg_211_);
v___x_212_ = lean_box(0);
v___x_213_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_211_, v___x_212_);
v___x_214_ = lean_bool_not(v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = l_Lake_Toml_digitFn(v_expected_207_, v_a_208_, v_s_210_);
return v___x_215_;
}
else
{
lean_dec(v_expected_207_);
return v_s_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object* v_expected_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_Toml_digitPairFn(v_expected_216_, v_a_217_, v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn(uint32_t v_c_220_, lean_object* v_expected_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_pos_224_; lean_object* v_toInputContext_225_; uint8_t v___x_226_; 
v_pos_224_ = lean_ctor_get(v_a_223_, 2);
v_toInputContext_225_ = lean_ctor_get(v_a_222_, 0);
v___x_226_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_225_, v_pos_224_);
if (v___x_226_ == 0)
{
lean_object* v_inputString_227_; uint32_t v_curr_228_; uint8_t v___x_229_; 
v_inputString_227_ = lean_ctor_get(v_toInputContext_225_, 0);
v_curr_228_ = lean_string_utf8_get_fast(v_inputString_227_, v_pos_224_);
v___x_229_ = lean_uint32_dec_eq(v_curr_228_, v_c_220_);
if (v___x_229_ == 0)
{
uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 1;
v___x_231_ = l_Lake_Toml_mkUnexpectedCharError(v_a_223_, v_curr_228_, v_expected_221_, v___x_230_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; 
lean_inc(v_pos_224_);
lean_dec(v_expected_221_);
v___x_232_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_223_, v_a_222_, v_pos_224_);
lean_dec(v_pos_224_);
return v___x_232_;
}
}
else
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Parser_ParserState_mkEOIError(v_a_223_, v_expected_221_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object* v_c_234_, lean_object* v_expected_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
uint32_t v_c_boxed_238_; lean_object* v_res_239_; 
v_c_boxed_238_ = lean_unbox_uint32(v_c_234_);
lean_dec(v_c_234_);
v_res_239_ = l_Lake_Toml_chFn(v_c_boxed_238_, v_expected_235_, v_a_236_, v_a_237_);
lean_dec_ref(v_a_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object* v_str_240_, lean_object* v_expected_241_, lean_object* v_strPos_242_, lean_object* v_c_243_, lean_object* v_s_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_string_utf8_at_end(v_str_240_, v_strPos_242_);
if (v___x_245_ == 0)
{
uint32_t v___x_246_; lean_object* v_s_247_; lean_object* v_errorMsg_248_; lean_object* v___x_249_; uint8_t v___x_250_; uint8_t v___x_251_; 
v___x_246_ = lean_string_utf8_get_fast(v_str_240_, v_strPos_242_);
lean_inc(v_expected_241_);
v_s_247_ = l_Lake_Toml_chFn(v___x_246_, v_expected_241_, v_c_243_, v_s_244_);
v_errorMsg_248_ = lean_ctor_get(v_s_247_, 4);
lean_inc(v_errorMsg_248_);
v___x_249_ = lean_box(0);
v___x_250_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_248_, v___x_249_);
v___x_251_ = lean_bool_not(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_string_utf8_next_fast(v_str_240_, v_strPos_242_);
lean_dec(v_strPos_242_);
v_strPos_242_ = v___x_252_;
v_s_244_ = v_s_247_;
goto _start;
}
else
{
lean_dec(v_strPos_242_);
lean_dec(v_expected_241_);
return v_s_247_;
}
}
else
{
lean_dec(v_strPos_242_);
lean_dec(v_expected_241_);
return v_s_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object* v_str_254_, lean_object* v_expected_255_, lean_object* v_strPos_256_, lean_object* v_c_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_Toml_strAuxFn(v_str_254_, v_expected_255_, v_strPos_256_, v_c_257_, v_s_258_);
lean_dec_ref(v_c_257_);
lean_dec_ref(v_str_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object* v_str_260_, lean_object* v_expected_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_alloc_closure((void*)(l_Lake_Toml_strAuxFn___boxed), 5, 3);
lean_closure_set(v___x_265_, 0, v_str_260_);
lean_closure_set(v___x_265_, 1, v_expected_261_);
lean_closure_set(v___x_265_, 2, v___x_264_);
v___x_266_ = l_Lean_Parser_atomicFn(v___x_265_, v_a_262_, v_a_263_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn(lean_object* v_p_268_, uint32_t v_sep_269_, lean_object* v_expected_270_, lean_object* v_c_271_, lean_object* v_s_272_){
_start:
{
lean_object* v_pos_273_; lean_object* v_toInputContext_274_; uint8_t v___x_275_; 
v_pos_273_ = lean_ctor_get(v_s_272_, 2);
v_toInputContext_274_ = lean_ctor_get(v_c_271_, 0);
v___x_275_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_274_, v_pos_273_);
if (v___x_275_ == 0)
{
lean_object* v_inputString_276_; uint32_t v_curr_277_; lean_object* v_s_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
lean_inc(v_pos_273_);
v_inputString_276_ = lean_ctor_get(v_toInputContext_274_, 0);
v_curr_277_ = lean_string_utf8_get_fast(v_inputString_276_, v_pos_273_);
v_s_278_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_272_, v_c_271_, v_pos_273_);
lean_dec(v_pos_273_);
v___x_279_ = lean_box_uint32(v_curr_277_);
lean_inc_ref(v_p_268_);
v___x_280_ = lean_apply_1(v_p_268_, v___x_279_);
v___x_281_ = lean_unbox(v___x_280_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; uint8_t v___x_283_; 
lean_dec_ref(v_p_268_);
v___x_282_ = 1;
v___x_283_ = lean_uint32_dec_eq(v_curr_277_, v_sep_269_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = l_Lake_Toml_mkUnexpectedCharError(v_s_278_, v_curr_277_, v_expected_270_, v___x_282_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_285_ = ((lean_object*)(l_Lake_Toml_sepByChar1Fn___closed__0));
v___x_286_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_287_ = lean_string_push(v___x_286_, v_curr_277_);
v___x_288_ = lean_string_append(v___x_285_, v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_290_ = lean_string_append(v___x_288_, v___x_289_);
v___x_291_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_278_, v___x_290_, v_expected_270_, v___x_282_);
return v___x_291_;
}
}
else
{
lean_object* v___x_292_; 
v___x_292_ = l_Lake_Toml_sepByChar1AuxFn(v_p_268_, v_sep_269_, v_expected_270_, v_c_271_, v_s_278_);
return v___x_292_;
}
}
else
{
lean_dec(v_expected_270_);
lean_dec_ref(v_p_268_);
return v_s_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object* v_p_293_, uint32_t v_sep_294_, lean_object* v_expected_295_, lean_object* v_c_296_, lean_object* v_s_297_){
_start:
{
lean_object* v_pos_298_; lean_object* v_toInputContext_299_; uint8_t v___x_300_; 
v_pos_298_ = lean_ctor_get(v_s_297_, 2);
v_toInputContext_299_ = lean_ctor_get(v_c_296_, 0);
v___x_300_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_299_, v_pos_298_);
if (v___x_300_ == 0)
{
lean_object* v_inputString_301_; uint32_t v_curr_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_inputString_301_ = lean_ctor_get(v_toInputContext_299_, 0);
v_curr_302_ = lean_string_utf8_get_fast(v_inputString_301_, v_pos_298_);
v___x_303_ = lean_box_uint32(v_curr_302_);
lean_inc_ref(v_p_293_);
v___x_304_ = lean_apply_1(v_p_293_, v___x_303_);
v___x_305_ = lean_unbox(v___x_304_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = lean_uint32_dec_eq(v_curr_302_, v_sep_294_);
if (v___x_306_ == 0)
{
lean_dec(v_expected_295_);
lean_dec_ref(v_p_293_);
return v_s_297_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc(v_pos_298_);
v___x_307_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_297_, v_c_296_, v_pos_298_);
lean_dec(v_pos_298_);
v___x_308_ = l_Lake_Toml_sepByChar1Fn(v_p_293_, v_sep_294_, v_expected_295_, v_c_296_, v___x_307_);
return v___x_308_;
}
}
else
{
lean_object* v___x_309_; 
lean_inc(v_pos_298_);
v___x_309_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_297_, v_c_296_, v_pos_298_);
lean_dec(v_pos_298_);
v_s_297_ = v___x_309_;
goto _start;
}
}
else
{
lean_dec(v_expected_295_);
lean_dec_ref(v_p_293_);
return v_s_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object* v_p_311_, lean_object* v_sep_312_, lean_object* v_expected_313_, lean_object* v_c_314_, lean_object* v_s_315_){
_start:
{
uint32_t v_sep_boxed_316_; lean_object* v_res_317_; 
v_sep_boxed_316_ = lean_unbox_uint32(v_sep_312_);
lean_dec(v_sep_312_);
v_res_317_ = l_Lake_Toml_sepByChar1AuxFn(v_p_311_, v_sep_boxed_316_, v_expected_313_, v_c_314_, v_s_315_);
lean_dec_ref(v_c_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object* v_p_318_, lean_object* v_sep_319_, lean_object* v_expected_320_, lean_object* v_c_321_, lean_object* v_s_322_){
_start:
{
uint32_t v_sep_boxed_323_; lean_object* v_res_324_; 
v_sep_boxed_323_ = lean_unbox_uint32(v_sep_319_);
lean_dec(v_sep_319_);
v_res_324_ = l_Lake_Toml_sepByChar1Fn(v_p_318_, v_sep_boxed_323_, v_expected_320_, v_c_321_, v_s_322_);
lean_dec_ref(v_c_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object* v_startPos_325_, lean_object* v_trailingFn_326_, lean_object* v_c_327_, lean_object* v_s_328_){
_start:
{
lean_object* v_toInputContext_329_; lean_object* v_pos_330_; lean_object* v_inputString_331_; lean_object* v_endPos_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_352_; 
v_toInputContext_329_ = lean_ctor_get(v_c_327_, 0);
lean_inc_ref(v_toInputContext_329_);
v_pos_330_ = lean_ctor_get(v_s_328_, 2);
lean_inc(v_pos_330_);
v_inputString_331_ = lean_ctor_get(v_toInputContext_329_, 0);
v_endPos_332_ = lean_ctor_get(v_toInputContext_329_, 3);
v_isSharedCheck_352_ = !lean_is_exclusive(v_toInputContext_329_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_353_ = lean_ctor_get(v_toInputContext_329_, 2);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_toInputContext_329_, 1);
lean_dec(v_unused_354_);
v___x_334_ = v_toInputContext_329_;
v_isShared_335_ = v_isSharedCheck_352_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_endPos_332_);
lean_inc(v_inputString_331_);
lean_dec(v_toInputContext_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_352_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_leading_336_; lean_object* v_s_337_; lean_object* v_pos_338_; lean_object* v_val_339_; lean_object* v___y_341_; uint8_t v___x_349_; 
lean_inc(v_startPos_325_);
v_leading_336_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_327_, v_startPos_325_);
v_s_337_ = lean_apply_2(v_trailingFn_326_, v_c_327_, v_s_328_);
v_pos_338_ = lean_ctor_get(v_s_337_, 2);
lean_inc(v_pos_338_);
v_val_339_ = lean_string_utf8_extract(v_inputString_331_, v_startPos_325_, v_pos_330_);
v___x_349_ = lean_nat_dec_le(v_pos_338_, v_endPos_332_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec(v_pos_338_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v_inputString_331_);
lean_ctor_set(v___x_350_, 1, v_pos_330_);
lean_ctor_set(v___x_350_, 2, v_endPos_332_);
v___y_341_ = v___x_350_;
goto v___jp_340_;
}
else
{
lean_object* v___x_351_; 
lean_dec(v_endPos_332_);
v___x_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_351_, 0, v_inputString_331_);
lean_ctor_set(v___x_351_, 1, v_pos_330_);
lean_ctor_set(v___x_351_, 2, v_pos_338_);
v___y_341_ = v___x_351_;
goto v___jp_340_;
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = lean_string_utf8_byte_size(v_val_339_);
v___x_343_ = lean_nat_add(v_startPos_325_, v___x_342_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v___x_343_);
lean_ctor_set(v___x_334_, 2, v___y_341_);
lean_ctor_set(v___x_334_, 1, v_startPos_325_);
lean_ctor_set(v___x_334_, 0, v_leading_336_);
v___x_345_ = v___x_334_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_leading_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_startPos_325_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v___y_341_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v___x_343_);
v___x_345_ = v_reuseFailAlloc_348_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v_atom_346_; lean_object* v___x_347_; 
v_atom_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_346_, 0, v___x_345_);
lean_ctor_set(v_atom_346_, 1, v_val_339_);
v___x_347_ = l_Lean_Parser_ParserState_pushSyntax(v_s_337_, v_atom_346_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object* v_p_355_, lean_object* v_trailingFn_356_, lean_object* v_c_357_, lean_object* v_s_358_){
_start:
{
lean_object* v_pos_359_; lean_object* v_s_360_; lean_object* v_errorMsg_361_; lean_object* v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; 
v_pos_359_ = lean_ctor_get(v_s_358_, 2);
lean_inc(v_pos_359_);
lean_inc_ref(v_c_357_);
v_s_360_ = lean_apply_2(v_p_355_, v_c_357_, v_s_358_);
v_errorMsg_361_ = lean_ctor_get(v_s_360_, 4);
lean_inc(v_errorMsg_361_);
v___x_362_ = lean_box(0);
v___x_363_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_361_, v___x_362_);
v___x_364_ = lean_bool_not(v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = l_Lake_Toml_pushAtom(v_pos_359_, v_trailingFn_356_, v_c_357_, v_s_360_);
return v___x_365_;
}
else
{
lean_dec(v_pos_359_);
lean_dec_ref(v_c_357_);
lean_dec_ref(v_trailingFn_356_);
return v_s_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object* v___y_366_){
_start:
{
lean_inc(v___y_366_);
return v___y_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lake_Toml_atom___lam__0(v___y_367_);
lean_dec(v___y_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object* v___y_369_){
_start:
{
lean_inc_ref(v___y_369_);
return v___y_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_Toml_atom___lam__1(v___y_370_);
lean_dec_ref(v___y_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object* v_p_378_, lean_object* v_trailingFn_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_381_ = lean_alloc_closure((void*)(l_Lake_Toml_atomFn), 4, 2);
lean_closure_set(v___x_381_, 0, v_p_378_);
lean_closure_set(v___x_381_, 1, v_trailingFn_379_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_stxTrav_386_; lean_object* v_cur_387_; lean_object* v___x_388_; 
v___x_385_ = lean_st_ref_get(v___y_383_);
v_stxTrav_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_stxTrav_386_);
lean_dec(v___x_385_);
v_cur_387_ = lean_ctor_get(v_stxTrav_386_, 0);
lean_inc(v_cur_387_);
lean_dec_ref(v_stxTrav_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_cur_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_389_);
lean_dec(v___y_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_393_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v_stxTrav_407_; lean_object* v_leadWord_408_; uint8_t v_leadWordIdent_409_; uint8_t v_isUngrouped_410_; uint8_t v_mustBeGrouped_411_; lean_object* v_stack_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_423_; 
v___x_406_ = lean_st_ref_take(v___y_404_);
v_stxTrav_407_ = lean_ctor_get(v___x_406_, 0);
v_leadWord_408_ = lean_ctor_get(v___x_406_, 1);
v_leadWordIdent_409_ = lean_ctor_get_uint8(v___x_406_, sizeof(void*)*3);
v_isUngrouped_410_ = lean_ctor_get_uint8(v___x_406_, sizeof(void*)*3 + 1);
v_mustBeGrouped_411_ = lean_ctor_get_uint8(v___x_406_, sizeof(void*)*3 + 2);
v_stack_412_ = lean_ctor_get(v___x_406_, 2);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_423_ == 0)
{
v___x_414_ = v___x_406_;
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_stack_412_);
lean_inc(v_leadWord_408_);
lean_inc(v_stxTrav_407_);
lean_dec(v___x_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = l_Lean_Syntax_Traverser_left(v_stxTrav_407_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_leadWord_408_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_stack_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_422_, sizeof(void*)*3, v_leadWordIdent_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_422_, sizeof(void*)*3 + 1, v_isUngrouped_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_422_, sizeof(void*)*3 + 2, v_mustBeGrouped_411_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_st_ref_set(v___y_404_, v___x_418_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_424_);
lean_dec(v___y_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_439_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set(v___x_444_, 3, v___x_443_);
lean_ctor_set(v___x_444_, 4, v___x_442_);
lean_ctor_set(v___x_444_, 5, v___x_442_);
lean_ctor_set(v___x_444_, 6, v___x_442_);
lean_ctor_set(v___x_444_, 7, v___x_442_);
lean_ctor_set(v___x_444_, 8, v___x_442_);
lean_ctor_set(v___x_444_, 9, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3);
v___x_453_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set(v___x_453_, 3, v___x_449_);
lean_ctor_set_usize(v___x_453_, 4, v___x_448_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_box(1);
v___x_455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(lean_object* v_msgData_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_options_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_462_ = lean_st_ref_get(v___y_460_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc_ref(v_env_463_);
lean_dec(v___x_462_);
v_options_464_ = lean_ctor_get(v___y_459_, 2);
v___x_465_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
v___x_466_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_464_);
v___x_467_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_467_, 0, v_env_463_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set(v___x_467_, 3, v_options_464_);
v___x_468_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_msgData_458_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(lean_object* v_msgData_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_474_;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_475_; double v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_float_of_nat(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* v_cls_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_ref_484_; lean_object* v___x_485_; lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_530_; 
v_ref_484_ = lean_ctor_get(v___y_481_, 5);
v___x_485_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_480_, v___y_481_, v___y_482_);
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_530_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_530_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_530_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v_traceState_491_; lean_object* v_env_492_; lean_object* v_nextMacroScope_493_; lean_object* v_ngen_494_; lean_object* v_auxDeclNGen_495_; lean_object* v_cache_496_; lean_object* v_messages_497_; lean_object* v_infoState_498_; lean_object* v_snapshotTasks_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_529_; 
v___x_490_ = lean_st_ref_take(v___y_482_);
v_traceState_491_ = lean_ctor_get(v___x_490_, 4);
v_env_492_ = lean_ctor_get(v___x_490_, 0);
v_nextMacroScope_493_ = lean_ctor_get(v___x_490_, 1);
v_ngen_494_ = lean_ctor_get(v___x_490_, 2);
v_auxDeclNGen_495_ = lean_ctor_get(v___x_490_, 3);
v_cache_496_ = lean_ctor_get(v___x_490_, 5);
v_messages_497_ = lean_ctor_get(v___x_490_, 6);
v_infoState_498_ = lean_ctor_get(v___x_490_, 7);
v_snapshotTasks_499_ = lean_ctor_get(v___x_490_, 8);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_529_ == 0)
{
v___x_501_ = v___x_490_;
v_isShared_502_ = v_isSharedCheck_529_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snapshotTasks_499_);
lean_inc(v_infoState_498_);
lean_inc(v_messages_497_);
lean_inc(v_cache_496_);
lean_inc(v_traceState_491_);
lean_inc(v_auxDeclNGen_495_);
lean_inc(v_ngen_494_);
lean_inc(v_nextMacroScope_493_);
lean_inc(v_env_492_);
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_529_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint64_t v_tid_503_; lean_object* v_traces_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_528_; 
v_tid_503_ = lean_ctor_get_uint64(v_traceState_491_, sizeof(void*)*1);
v_traces_504_ = lean_ctor_get(v_traceState_491_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_traceState_491_);
if (v_isSharedCheck_528_ == 0)
{
v___x_506_ = v_traceState_491_;
v_isShared_507_ = v_isSharedCheck_528_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_traces_504_);
lean_dec(v_traceState_491_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_528_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; double v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_508_ = lean_box(0);
v___x_509_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_510_ = 0;
v___x_511_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_512_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_512_, 0, v_cls_479_);
lean_ctor_set(v___x_512_, 1, v___x_508_);
lean_ctor_set(v___x_512_, 2, v___x_511_);
lean_ctor_set_float(v___x_512_, sizeof(void*)*3, v___x_509_);
lean_ctor_set_float(v___x_512_, sizeof(void*)*3 + 8, v___x_509_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*3 + 16, v___x_510_);
v___x_513_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_514_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v_a_486_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
lean_inc(v_ref_484_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_ref_484_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_PersistentArray_push___redArg(v_traces_504_, v___x_515_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_516_);
v___x_518_ = v___x_506_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_516_);
lean_ctor_set_uint64(v_reuseFailAlloc_527_, sizeof(void*)*1, v_tid_503_);
v___x_518_ = v_reuseFailAlloc_527_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v___x_518_);
v___x_520_ = v___x_501_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_env_492_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_nextMacroScope_493_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_ngen_494_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_auxDeclNGen_495_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_526_, 5, v_cache_496_);
lean_ctor_set(v_reuseFailAlloc_526_, 6, v_messages_497_);
lean_ctor_set(v_reuseFailAlloc_526_, 7, v_infoState_498_);
lean_ctor_set(v_reuseFailAlloc_526_, 8, v_snapshotTasks_499_);
v___x_520_ = v_reuseFailAlloc_526_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_521_ = lean_st_ref_set(v___y_482_, v___x_520_);
v___x_522_ = lean_box(0);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_522_);
v___x_524_ = v___x_488_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_531_, lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_531_, v_msg_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_536_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_548_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__5));
v___x_549_ = l_Lean_Name_append(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__8(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__7));
v___x_552_ = l_Lean_stringToMessageData(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__10(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__9));
v___x_555_ = l_Lean_stringToMessageData(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; lean_object* v_a_562_; 
v___x_561_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_557_);
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref(v___x_561_);
if (lean_obj_tag(v_a_562_) == 2)
{
lean_object* v_info_563_; lean_object* v_val_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_info_563_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_info_563_);
v_val_564_ = lean_ctor_get(v_a_562_, 1);
lean_inc_ref(v_val_564_);
v___x_565_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_562_);
lean_dec_ref_known(v_a_562_, 2);
v___x_566_ = 0;
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_568_, 0, v_info_563_);
lean_closure_set(v___x_568_, 1, v_val_564_);
lean_closure_set(v___x_568_, 2, v___x_567_);
v___x_569_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_565_, v___x_568_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v___x_565_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
lean_dec_ref_known(v___x_569_, 1);
v___x_570_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_557_);
return v___x_570_;
}
else
{
return v___x_569_;
}
}
else
{
lean_object* v_options_571_; uint8_t v_hasTrace_572_; 
v_options_571_ = lean_ctor_get(v_a_558_, 2);
v_hasTrace_572_ = lean_ctor_get_uint8(v_options_571_, sizeof(void*)*1);
if (v_hasTrace_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v_a_562_);
v___x_573_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_573_;
}
else
{
lean_object* v_inheritedTraceOptions_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_inheritedTraceOptions_574_ = lean_ctor_get(v_a_558_, 13);
v___x_575_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_576_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_577_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_574_, v_options_571_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_a_562_);
v___x_578_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_579_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_580_ = lean_box(0);
v___x_581_ = 0;
v___x_582_ = l_Lean_Syntax_formatStx(v_a_562_, v___x_580_, v___x_581_);
v___x_583_ = l_Lean_MessageData_ofFormat(v___x_582_);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_575_, v___x_586_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref_known(v___x_587_, 1);
v___x_588_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_588_;
}
else
{
return v___x_587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lake_Toml_atom_formatter___redArg(v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lake_Toml_atom_formatter___redArg(v_a_597_, v_a_598_, v_a_599_, v_a_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_Toml_atom_formatter(v_x_603_, v_x_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec_ref(v_x_604_);
lean_dec_ref(v_x_603_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_611_, lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_611_, v_msg_612_, v___y_615_, v___y_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_619_, lean_object* v_msg_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_619_, v_msg_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_630_);
lean_dec(v_a_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_641_, v_x_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec_ref(v_x_642_);
lean_dec_ref(v_x_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_649_, lean_object* v_expected_650_, lean_object* v_trailingFn_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_box_uint32(v_c_649_);
v___x_653_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_653_, 0, v___x_652_);
lean_closure_set(v___x_653_, 1, v_expected_650_);
v___x_654_ = l_Lake_Toml_atom(v___x_653_, v_trailingFn_651_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_655_, lean_object* v_expected_656_, lean_object* v_trailingFn_657_){
_start:
{
uint32_t v_c_boxed_658_; lean_object* v_res_659_; 
v_c_boxed_658_ = lean_unbox_uint32(v_c_655_);
lean_dec(v_c_655_);
v_res_659_ = l_Lake_Toml_chAtom(v_c_boxed_658_, v_expected_656_, v_trailingFn_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
uint8_t v___x_666_; lean_object* v___x_667_; 
v___x_666_ = 0;
v___x_667_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_660_, v___x_666_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
uint32_t v_c_boxed_674_; lean_object* v_res_675_; 
v_c_boxed_674_ = lean_unbox_uint32(v_c_668_);
lean_dec(v_c_668_);
v_res_675_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_674_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_676_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
uint32_t v_c_boxed_693_; lean_object* v_res_694_; 
v_c_boxed_693_ = lean_unbox_uint32(v_c_685_);
lean_dec(v_c_685_);
v_res_694_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_693_, v_x_686_, v_x_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec_ref(v_x_687_);
lean_dec(v_x_686_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_698_);
lean_dec(v_a_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_705_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
uint32_t v_x_18__boxed_718_; lean_object* v_res_719_; 
v_x_18__boxed_718_ = lean_unbox_uint32(v_x_710_);
lean_dec(v_x_710_);
v_res_719_ = l_Lake_Toml_chAtom_parenthesizer(v_x_18__boxed_718_, v_x_711_, v_x_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_x_712_);
lean_dec(v_x_711_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_720_, lean_object* v_expected_721_, lean_object* v_trailingFn_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_str_727_; lean_object* v_startInclusive_728_; lean_object* v_endExclusive_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_string_utf8_byte_size(v_s_720_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v_s_720_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = l_String_Slice_trimAscii(v___x_725_);
v_str_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_str_727_);
v_startInclusive_728_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_startInclusive_728_);
v_endExclusive_729_ = lean_ctor_get(v___x_726_, 2);
lean_inc(v_endExclusive_729_);
lean_dec_ref(v___x_726_);
v___x_730_ = lean_string_utf8_extract(v_str_727_, v_startInclusive_728_, v_endExclusive_729_);
lean_dec(v_endExclusive_729_);
lean_dec(v_startInclusive_728_);
lean_dec_ref(v_str_727_);
v___x_731_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_731_, 0, v___x_730_);
lean_closure_set(v___x_731_, 1, v_expected_721_);
v___x_732_ = l_Lake_Toml_atom(v___x_731_, v_trailingFn_722_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_747_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lake_Toml_strAtom_formatter(v_s_756_, v_x_757_, v_x_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec_ref(v_x_758_);
lean_dec(v_x_757_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_768_);
lean_dec(v_a_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_Toml_strAtom_parenthesizer(v_x_780_, v_x_781_, v_x_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_x_782_);
lean_dec(v_x_781_);
lean_dec_ref(v_x_780_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_789_, lean_object* v_startPos_790_, lean_object* v_trailingFn_791_, lean_object* v_c_792_, lean_object* v_s_793_){
_start:
{
lean_object* v_toInputContext_794_; lean_object* v_pos_795_; lean_object* v_inputString_796_; lean_object* v_endPos_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_815_; 
v_toInputContext_794_ = lean_ctor_get(v_c_792_, 0);
lean_inc_ref(v_toInputContext_794_);
v_pos_795_ = lean_ctor_get(v_s_793_, 2);
lean_inc(v_pos_795_);
v_inputString_796_ = lean_ctor_get(v_toInputContext_794_, 0);
v_endPos_797_ = lean_ctor_get(v_toInputContext_794_, 3);
v_isSharedCheck_815_ = !lean_is_exclusive(v_toInputContext_794_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_816_ = lean_ctor_get(v_toInputContext_794_, 2);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_toInputContext_794_, 1);
lean_dec(v_unused_817_);
v___x_799_ = v_toInputContext_794_;
v_isShared_800_ = v_isSharedCheck_815_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_endPos_797_);
lean_inc(v_inputString_796_);
lean_dec(v_toInputContext_794_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_815_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_leading_801_; lean_object* v_s_802_; lean_object* v_pos_803_; lean_object* v_val_804_; lean_object* v___y_806_; uint8_t v___x_812_; 
lean_inc(v_startPos_790_);
v_leading_801_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_792_, v_startPos_790_);
v_s_802_ = lean_apply_2(v_trailingFn_791_, v_c_792_, v_s_793_);
v_pos_803_ = lean_ctor_get(v_s_802_, 2);
lean_inc(v_pos_803_);
v_val_804_ = lean_string_utf8_extract(v_inputString_796_, v_startPos_790_, v_pos_795_);
v___x_812_ = lean_nat_dec_le(v_pos_803_, v_endPos_797_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v_pos_803_);
lean_inc(v_pos_795_);
v___x_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_813_, 0, v_inputString_796_);
lean_ctor_set(v___x_813_, 1, v_pos_795_);
lean_ctor_set(v___x_813_, 2, v_endPos_797_);
v___y_806_ = v___x_813_;
goto v___jp_805_;
}
else
{
lean_object* v___x_814_; 
lean_dec(v_endPos_797_);
lean_inc(v_pos_795_);
v___x_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_814_, 0, v_inputString_796_);
lean_ctor_set(v___x_814_, 1, v_pos_795_);
lean_ctor_set(v___x_814_, 2, v_pos_803_);
v___y_806_ = v___x_814_;
goto v___jp_805_;
}
v___jp_805_:
{
lean_object* v_info_808_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 3, v_pos_795_);
lean_ctor_set(v___x_799_, 2, v___y_806_);
lean_ctor_set(v___x_799_, 1, v_startPos_790_);
lean_ctor_set(v___x_799_, 0, v_leading_801_);
v_info_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_leading_801_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_startPos_790_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___y_806_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_pos_795_);
v_info_808_ = v_reuseFailAlloc_811_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Lean_Syntax_mkLit(v_kind_789_, v_val_804_, v_info_808_);
v___x_810_ = l_Lean_Parser_ParserState_pushSyntax(v_s_802_, v___x_809_);
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_818_, lean_object* v_p_819_, lean_object* v_trailingFn_820_, lean_object* v_c_821_, lean_object* v_s_822_){
_start:
{
lean_object* v_pos_823_; lean_object* v_s_824_; lean_object* v_errorMsg_825_; lean_object* v___x_826_; uint8_t v___x_827_; uint8_t v___x_828_; 
v_pos_823_ = lean_ctor_get(v_s_822_, 2);
lean_inc(v_pos_823_);
lean_inc_ref(v_c_821_);
v_s_824_ = lean_apply_2(v_p_819_, v_c_821_, v_s_822_);
v_errorMsg_825_ = lean_ctor_get(v_s_824_, 4);
lean_inc(v_errorMsg_825_);
v___x_826_ = lean_box(0);
v___x_827_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_825_, v___x_826_);
v___x_828_ = lean_bool_not(v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
v___x_829_ = l_Lake_Toml_pushLit(v_kind_818_, v_pos_823_, v_trailingFn_820_, v_c_821_, v_s_824_);
return v___x_829_;
}
else
{
lean_dec(v_pos_823_);
lean_dec_ref(v_c_821_);
lean_dec_ref(v_trailingFn_820_);
lean_dec(v_kind_818_);
return v_s_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_830_, lean_object* v_p_831_, lean_object* v_trailingFn_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_834_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_834_, 0, v_kind_830_);
lean_closure_set(v___x_834_, 1, v_p_831_);
lean_closure_set(v___x_834_, 2, v_trailingFn_832_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lake_Toml_lit_formatter___redArg(v_kind_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_850_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lake_Toml_lit_formatter(v_kind_859_, v_x_860_, v_x_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_x_861_);
lean_dec_ref(v_x_860_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_871_);
lean_dec(v_a_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_878_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lake_Toml_lit_parenthesizer(v_x_883_, v_x_884_, v_x_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec_ref(v_x_885_);
lean_dec_ref(v_x_884_);
lean_dec(v_x_883_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_906_, lean_object* v_kind_907_, uint8_t v_anonymous_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___f_914_; uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc(v_kind_907_);
v___f_914_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_914_, 0, v_kind_907_);
v___x_915_ = 0;
v___x_916_ = lean_box(v_anonymous_908_);
v___x_917_ = lean_box(v___x_915_);
v___x_918_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_918_, 0, v_name_906_);
lean_closure_set(v___x_918_, 1, v_kind_907_);
lean_closure_set(v___x_918_, 2, v___x_916_);
lean_closure_set(v___x_918_, 3, v___x_917_);
v___x_919_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_918_, v___f_914_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_920_, lean_object* v_kind_921_, lean_object* v_anonymous_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
uint8_t v_anonymous_boxed_928_; lean_object* v_res_929_; 
v_anonymous_boxed_928_ = lean_unbox(v_anonymous_922_);
v_res_929_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_920_, v_kind_921_, v_anonymous_boxed_928_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_930_, lean_object* v_kind_931_, lean_object* v_p_932_, lean_object* v_trailingFn_933_, uint8_t v_anonymous_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_930_, v_kind_931_, v_anonymous_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_941_, lean_object* v_kind_942_, lean_object* v_p_943_, lean_object* v_trailingFn_944_, lean_object* v_anonymous_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
uint8_t v_anonymous_boxed_951_; lean_object* v_res_952_; 
v_anonymous_boxed_951_ = lean_unbox(v_anonymous_945_);
v_res_952_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_941_, v_kind_942_, v_p_943_, v_trailingFn_944_, v_anonymous_boxed_951_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec_ref(v_trailingFn_944_);
lean_dec_ref(v_p_943_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_954_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_966_, lean_object* v_kind_967_, uint8_t v_anonymous_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___f_974_; uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___f_974_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_975_ = 0;
v___x_976_ = lean_box(v_anonymous_968_);
v___x_977_ = lean_box(v___x_975_);
v___x_978_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_978_, 0, v_name_966_);
lean_closure_set(v___x_978_, 1, v_kind_967_);
lean_closure_set(v___x_978_, 2, v___x_976_);
lean_closure_set(v___x_978_, 3, v___x_977_);
v___x_979_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_978_, v___f_974_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_980_, lean_object* v_kind_981_, lean_object* v_anonymous_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
uint8_t v_anonymous_boxed_988_; lean_object* v_res_989_; 
v_anonymous_boxed_988_ = lean_unbox(v_anonymous_982_);
v_res_989_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_980_, v_kind_981_, v_anonymous_boxed_988_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_990_, lean_object* v_kind_991_, lean_object* v_p_992_, lean_object* v_trailingFn_993_, uint8_t v_anonymous_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_990_, v_kind_991_, v_anonymous_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_1001_, lean_object* v_kind_1002_, lean_object* v_p_1003_, lean_object* v_trailingFn_1004_, lean_object* v_anonymous_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_anonymous_boxed_1011_; lean_object* v_res_1012_; 
v_anonymous_boxed_1011_ = lean_unbox(v_anonymous_1005_);
v_res_1012_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_1001_, v_kind_1002_, v_p_1003_, v_trailingFn_1004_, v_anonymous_boxed_1011_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec_ref(v_trailingFn_1004_);
lean_dec_ref(v_p_1003_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1013_, lean_object* v_kind_1014_, lean_object* v_p_1015_, lean_object* v_trailingFn_1016_, uint8_t v_anonymous_1017_){
_start:
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = 0;
lean_inc(v_kind_1014_);
v___x_1019_ = l_Lean_Parser_mkAntiquot(v_name_1013_, v_kind_1014_, v_anonymous_1017_, v___x_1018_);
v___x_1020_ = l_Lake_Toml_lit(v_kind_1014_, v_p_1015_, v_trailingFn_1016_);
v___x_1021_ = l_Lean_Parser_withAntiquot(v___x_1019_, v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1022_, lean_object* v_kind_1023_, lean_object* v_p_1024_, lean_object* v_trailingFn_1025_, lean_object* v_anonymous_1026_){
_start:
{
uint8_t v_anonymous_boxed_1027_; lean_object* v_res_1028_; 
v_anonymous_boxed_1027_ = lean_unbox(v_anonymous_1026_);
v_res_1028_ = l_Lake_Toml_litWithAntiquot(v_name_1022_, v_kind_1023_, v_p_1024_, v_trailingFn_1025_, v_anonymous_boxed_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = l_Lean_Parser_epsilonInfo;
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_fn_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lake_Toml_epsilon_formatter(v_x_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec_ref(v_x_1044_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec_ref(v_x_1063_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1070_, lean_object* v_x_1071_){
_start:
{
switch(lean_obj_tag(v_x_1071_))
{
case 2:
{
lean_object* v_info_1072_; lean_object* v_val_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_info_1072_ = lean_ctor_get(v_x_1071_, 0);
v_val_1073_ = lean_ctor_get(v_x_1071_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v_x_1071_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_val_1073_);
lean_inc(v_info_1072_);
lean_dec(v_x_1071_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_apply_1(v_f_1070_, v_info_1072_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_val_1073_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
case 3:
{
lean_object* v_info_1082_; lean_object* v_rawVal_1083_; lean_object* v_val_1084_; lean_object* v_preresolved_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_info_1082_ = lean_ctor_get(v_x_1071_, 0);
v_rawVal_1083_ = lean_ctor_get(v_x_1071_, 1);
v_val_1084_ = lean_ctor_get(v_x_1071_, 2);
v_preresolved_1085_ = lean_ctor_get(v_x_1071_, 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v_x_1071_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_preresolved_1085_);
lean_inc(v_val_1084_);
lean_inc(v_rawVal_1083_);
lean_inc(v_info_1082_);
lean_dec(v_x_1071_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_apply_1(v_f_1070_, v_info_1082_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_rawVal_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_val_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_preresolved_1085_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
case 1:
{
lean_object* v_info_1094_; lean_object* v_kind_1095_; lean_object* v_args_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_info_1094_ = lean_ctor_get(v_x_1071_, 0);
v_kind_1095_ = lean_ctor_get(v_x_1071_, 1);
v_args_1096_ = lean_ctor_get(v_x_1071_, 2);
v___x_1097_ = lean_array_get_size(v_args_1096_);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_sub(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_nat_dec_lt(v___x_1099_, v___x_1097_);
if (v___x_1100_ == 0)
{
lean_dec(v___x_1099_);
lean_dec_ref(v_f_1070_);
return v_x_1071_;
}
else
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1112_; 
lean_inc_ref(v_args_1096_);
lean_inc(v_kind_1095_);
lean_inc(v_info_1094_);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1113_ = lean_ctor_get(v_x_1071_, 2);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_x_1071_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_x_1071_, 0);
lean_dec(v_unused_1115_);
v___x_1102_ = v_x_1071_;
v_isShared_1103_ = v_isSharedCheck_1112_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_x_1071_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1112_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_v_1104_; lean_object* v___x_1105_; lean_object* v_xs_x27_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v_v_1104_ = lean_array_fget(v_args_1096_, v___x_1099_);
v___x_1105_ = lean_box(0);
v_xs_x27_1106_ = lean_array_fset(v_args_1096_, v___x_1099_, v___x_1105_);
v___x_1107_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1070_, v_v_1104_);
v___x_1108_ = lean_array_fset(v_xs_x27_1106_, v___x_1099_, v___x_1107_);
lean_dec(v___x_1099_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 2, v___x_1108_);
v___x_1110_ = v___x_1102_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_info_1094_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_kind_1095_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1070_);
return v_x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1116_, lean_object* v_x_1117_){
_start:
{
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_object* v_trailing_1118_; lean_object* v_leading_1119_; lean_object* v_pos_1120_; lean_object* v_endPos_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1138_; 
v_trailing_1118_ = lean_ctor_get(v_x_1117_, 2);
v_leading_1119_ = lean_ctor_get(v_x_1117_, 0);
v_pos_1120_ = lean_ctor_get(v_x_1117_, 1);
v_endPos_1121_ = lean_ctor_get(v_x_1117_, 3);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1117_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1123_ = v_x_1117_;
v_isShared_1124_ = v_isSharedCheck_1138_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_endPos_1121_);
lean_inc(v_trailing_1118_);
lean_inc(v_pos_1120_);
lean_inc(v_leading_1119_);
lean_dec(v_x_1117_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1138_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_str_1125_; lean_object* v_startPos_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1136_; 
v_str_1125_ = lean_ctor_get(v_trailing_1118_, 0);
v_startPos_1126_ = lean_ctor_get(v_trailing_1118_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_trailing_1118_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_trailing_1118_, 2);
lean_dec(v_unused_1137_);
v___x_1128_ = v_trailing_1118_;
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_startPos_1126_);
lean_inc(v_str_1125_);
lean_dec(v_trailing_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v_stopPos_1116_);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_str_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_startPos_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_stopPos_1116_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 2, v___x_1131_);
v___x_1133_ = v___x_1123_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_leading_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_pos_1120_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_endPos_1121_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_dec(v_stopPos_1116_);
return v_x_1117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1139_, lean_object* v_x_1140_){
_start:
{
switch(lean_obj_tag(v_x_1140_))
{
case 2:
{
lean_object* v_info_1141_; lean_object* v_val_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_info_1141_ = lean_ctor_get(v_x_1140_, 0);
v_val_1142_ = lean_ctor_get(v_x_1140_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v_x_1140_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_val_1142_);
lean_inc(v_info_1141_);
lean_dec(v_x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1139_, v_info_1141_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_val_1142_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
case 3:
{
lean_object* v_info_1151_; lean_object* v_rawVal_1152_; lean_object* v_val_1153_; lean_object* v_preresolved_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
v_info_1151_ = lean_ctor_get(v_x_1140_, 0);
v_rawVal_1152_ = lean_ctor_get(v_x_1140_, 1);
v_val_1153_ = lean_ctor_get(v_x_1140_, 2);
v_preresolved_1154_ = lean_ctor_get(v_x_1140_, 3);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1156_ = v_x_1140_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_preresolved_1154_);
lean_inc(v_val_1153_);
lean_inc(v_rawVal_1152_);
lean_inc(v_info_1151_);
lean_dec(v_x_1140_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1139_, v_info_1151_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_rawVal_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_val_1153_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_preresolved_1154_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
case 1:
{
lean_object* v_info_1163_; lean_object* v_kind_1164_; lean_object* v_args_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_info_1163_ = lean_ctor_get(v_x_1140_, 0);
v_kind_1164_ = lean_ctor_get(v_x_1140_, 1);
v_args_1165_ = lean_ctor_get(v_x_1140_, 2);
v___x_1166_ = lean_array_get_size(v_args_1165_);
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_sub(v___x_1166_, v___x_1167_);
v___x_1169_ = lean_nat_dec_lt(v___x_1168_, v___x_1166_);
if (v___x_1169_ == 0)
{
lean_dec(v___x_1168_);
lean_dec(v_stopPos_1139_);
return v_x_1140_;
}
else
{
lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1181_; 
lean_inc_ref(v_args_1165_);
lean_inc(v_kind_1164_);
lean_inc(v_info_1163_);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; lean_object* v_unused_1183_; lean_object* v_unused_1184_; 
v_unused_1182_ = lean_ctor_get(v_x_1140_, 2);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_x_1140_, 1);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_x_1140_, 0);
lean_dec(v_unused_1184_);
v___x_1171_ = v_x_1140_;
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
else
{
lean_dec(v_x_1140_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_v_1173_; lean_object* v___x_1174_; lean_object* v_xs_x27_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v_v_1173_ = lean_array_fget(v_args_1165_, v___x_1168_);
v___x_1174_ = lean_box(0);
v_xs_x27_1175_ = lean_array_fset(v_args_1165_, v___x_1168_, v___x_1174_);
v___x_1176_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1139_, v_v_1173_);
v___x_1177_ = lean_array_fset(v_xs_x27_1175_, v___x_1168_, v___x_1176_);
lean_dec(v___x_1168_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 2, v___x_1177_);
v___x_1179_ = v___x_1171_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_info_1163_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_kind_1164_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1139_);
return v_x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1185_, lean_object* v_c_1186_, lean_object* v_s_1187_){
_start:
{
lean_object* v_s_1188_; lean_object* v_stxStack_1189_; lean_object* v_pos_1190_; lean_object* v_tail_1191_; lean_object* v_s_1192_; lean_object* v_tail_1193_; lean_object* v___x_1194_; 
v_s_1188_ = lean_apply_2(v_p_1185_, v_c_1186_, v_s_1187_);
v_stxStack_1189_ = lean_ctor_get(v_s_1188_, 0);
lean_inc_ref(v_stxStack_1189_);
v_pos_1190_ = lean_ctor_get(v_s_1188_, 2);
lean_inc(v_pos_1190_);
v_tail_1191_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1189_);
lean_dec_ref(v_stxStack_1189_);
v_s_1192_ = l_Lean_Parser_ParserState_popSyntax(v_s_1188_);
v_tail_1193_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1190_, v_tail_1191_);
v___x_1194_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1192_, v_tail_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lake_Toml_trailing_formatter(v_p_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec_ref(v_p_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lake_Toml_trailing_parenthesizer(v_p_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec_ref(v_p_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1232_, 0, v_p_1231_);
v___x_1233_ = l_Lean_Parser_epsilonInfo;
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_p_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1239_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = l_Lean_Syntax_getKind(v_a_1244_);
v___x_1246_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1245_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lake_Toml_dynamicNode_formatter(v_x_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_x_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; lean_object* v_stxTrav_1270_; lean_object* v_cur_1271_; lean_object* v___x_1272_; 
v___x_1269_ = lean_st_ref_get(v___y_1267_);
v_stxTrav_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_ref(v_stxTrav_1270_);
lean_dec(v___x_1269_);
v_cur_1271_ = lean_ctor_get(v_stxTrav_1270_, 0);
lean_inc(v_cur_1271_);
lean_dec_ref(v_stxTrav_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_cur_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1273_);
lean_dec(v___y_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1277_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1289_);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = l_Lean_Syntax_getKind(v_a_1294_);
v___x_1296_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1295_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_x_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_fn_1323_; lean_object* v___x_1324_; 
lean_inc_ref(v_f_1317_);
v___x_1320_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1320_, 0, v_f_1317_);
v___x_1321_ = l_Lake_Toml_dynamicNode(v___x_1320_);
v___x_1322_ = lean_apply_1(v_f_1317_, v___x_1321_);
v_fn_1323_ = lean_ctor_get(v___x_1322_, 1);
lean_inc_ref(v_fn_1323_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = lean_apply_2(v_fn_1323_, v_a_1318_, v_a_1319_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lake_Toml_recNode_formatter(v_f_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_f_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lake_Toml_recNode_parenthesizer(v_f_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec_ref(v_f_1370_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1378_, 0, v_f_1377_);
v___x_1379_ = l_Lake_Toml_dynamicNode(v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1380_, lean_object* v_kind_1381_, lean_object* v_f_1382_, uint8_t v_anonymous_1383_, lean_object* v_p_1384_){
_start:
{
uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1385_ = 1;
lean_inc(v_kind_1381_);
v___x_1386_ = l_Lean_Parser_mkAntiquot(v_name_1380_, v_kind_1381_, v_anonymous_1383_, v___x_1385_);
v___x_1387_ = lean_apply_1(v_f_1382_, v_p_1384_);
v___x_1388_ = l_Lean_Parser_withAntiquot(v___x_1386_, v___x_1387_);
v___x_1389_ = l_Lean_Parser_withCache(v_kind_1381_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1390_, lean_object* v_kind_1391_, lean_object* v_f_1392_, lean_object* v_anonymous_1393_, lean_object* v_p_1394_){
_start:
{
uint8_t v_anonymous_boxed_1395_; lean_object* v_res_1396_; 
v_anonymous_boxed_1395_ = lean_unbox(v_anonymous_1393_);
v_res_1396_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1390_, v_kind_1391_, v_f_1392_, v_anonymous_boxed_1395_, v_p_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1397_, lean_object* v_kind_1398_, lean_object* v_f_1399_, uint8_t v_anonymous_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1406_ = 1;
v___x_1407_ = lean_box(v_anonymous_1400_);
v___x_1408_ = lean_box(v___x_1406_);
lean_inc(v_kind_1398_);
lean_inc_ref(v_name_1397_);
v___x_1409_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1409_, 0, v_name_1397_);
lean_closure_set(v___x_1409_, 1, v_kind_1398_);
lean_closure_set(v___x_1409_, 2, v___x_1407_);
lean_closure_set(v___x_1409_, 3, v___x_1408_);
v___x_1410_ = lean_box(v_anonymous_1400_);
v___x_1411_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1411_, 0, v_name_1397_);
lean_closure_set(v___x_1411_, 1, v_kind_1398_);
lean_closure_set(v___x_1411_, 2, v_f_1399_);
lean_closure_set(v___x_1411_, 3, v___x_1410_);
v___x_1412_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1412_, 0, v___x_1411_);
v___x_1413_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1409_, v___x_1412_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1414_, lean_object* v_kind_1415_, lean_object* v_f_1416_, lean_object* v_anonymous_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
uint8_t v_anonymous_boxed_1423_; lean_object* v_res_1424_; 
v_anonymous_boxed_1423_ = lean_unbox(v_anonymous_1417_);
v_res_1424_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1414_, v_kind_1415_, v_f_1416_, v_anonymous_boxed_1423_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1425_, lean_object* v_kind_1426_, lean_object* v_f_1427_, uint8_t v_anonymous_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1434_ = 1;
v___x_1435_ = lean_box(v_anonymous_1428_);
v___x_1436_ = lean_box(v___x_1434_);
lean_inc(v_kind_1426_);
lean_inc_ref(v_name_1425_);
v___x_1437_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1437_, 0, v_name_1425_);
lean_closure_set(v___x_1437_, 1, v_kind_1426_);
lean_closure_set(v___x_1437_, 2, v___x_1435_);
lean_closure_set(v___x_1437_, 3, v___x_1436_);
v___x_1438_ = lean_box(v_anonymous_1428_);
v___x_1439_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1439_, 0, v_name_1425_);
lean_closure_set(v___x_1439_, 1, v_kind_1426_);
lean_closure_set(v___x_1439_, 2, v_f_1427_);
lean_closure_set(v___x_1439_, 3, v___x_1438_);
v___x_1440_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1440_, 0, v___x_1439_);
v___x_1441_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1437_, v___x_1440_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1442_, lean_object* v_kind_1443_, lean_object* v_f_1444_, lean_object* v_anonymous_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
uint8_t v_anonymous_boxed_1451_; lean_object* v_res_1452_; 
v_anonymous_boxed_1451_ = lean_unbox(v_anonymous_1445_);
v_res_1452_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1442_, v_kind_1443_, v_f_1444_, v_anonymous_boxed_1451_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1453_, lean_object* v_kind_1454_, lean_object* v_f_1455_, uint8_t v_anonymous_1456_){
_start:
{
uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1457_ = 1;
lean_inc_n(v_kind_1454_, 2);
lean_inc_ref(v_name_1453_);
v___x_1458_ = l_Lean_Parser_mkAntiquot(v_name_1453_, v_kind_1454_, v_anonymous_1456_, v___x_1457_);
v___x_1459_ = lean_box(v_anonymous_1456_);
v___x_1460_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1460_, 0, v_name_1453_);
lean_closure_set(v___x_1460_, 1, v_kind_1454_);
lean_closure_set(v___x_1460_, 2, v_f_1455_);
lean_closure_set(v___x_1460_, 3, v___x_1459_);
v___x_1461_ = l_Lake_Toml_recNode(v___x_1460_);
v___x_1462_ = l_Lean_Parser_withAntiquot(v___x_1458_, v___x_1461_);
v___x_1463_ = l_Lean_Parser_withCache(v_kind_1454_, v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1464_, lean_object* v_kind_1465_, lean_object* v_f_1466_, lean_object* v_anonymous_1467_){
_start:
{
uint8_t v_anonymous_boxed_1468_; lean_object* v_res_1469_; 
v_anonymous_boxed_1468_ = lean_unbox(v_anonymous_1467_);
v_res_1469_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1464_, v_kind_1465_, v_f_1466_, v_anonymous_boxed_1468_);
return v_res_1469_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___f_1477_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1478_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1479_, 0, v___x_1478_);
lean_closure_set(v___x_1479_, 1, v___f_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1486_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1487_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1488_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1488_, 0, v___x_1486_);
lean_closure_set(v___x_1488_, 1, v_p_1480_);
lean_closure_set(v___x_1488_, 2, v___x_1487_);
v___x_1489_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1490_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1488_, v___x_1489_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1498_, uint8_t v_allowTrailingLinebreak_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1498_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1506_, lean_object* v_allowTrailingLinebreak_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1513_; lean_object* v_res_1514_; 
v_allowTrailingLinebreak_boxed_1513_ = lean_unbox(v_allowTrailingLinebreak_1507_);
v_res_1514_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1506_, v_allowTrailingLinebreak_boxed_1513_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___f_1518_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1519_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1520_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1520_, 0, v___x_1519_);
lean_closure_set(v___x_1520_, 1, v___f_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1527_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1528_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1529_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1529_, 0, v___x_1527_);
lean_closure_set(v___x_1529_, 1, v_p_1521_);
lean_closure_set(v___x_1529_, 2, v___x_1528_);
v___x_1530_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1531_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1529_, v___x_1530_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1539_, uint8_t v_allowTrailingLinebreak_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1539_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1547_, lean_object* v_allowTrailingLinebreak_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1554_; lean_object* v_res_1555_; 
v_allowTrailingLinebreak_boxed_1554_ = lean_unbox(v_allowTrailingLinebreak_1548_);
v_res_1555_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1547_, v_allowTrailingLinebreak_boxed_1554_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
return v_res_1555_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1557_ = l_Lean_Parser_symbol(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1560_ = l_Lean_Parser_checkLinebreakBefore(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = l_Lean_Parser_pushNone;
v___x_1562_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1563_ = l_Lean_Parser_andthen(v___x_1562_, v___x_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1564_, uint8_t v_allowTrailingLinebreak_1565_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_p_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1566_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1567_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1568_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1566_, v_p_1564_, v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1570_ = l_Lean_Parser_sepByNoAntiquot(v_p_1568_, v___x_1569_, v_allowTrailingLinebreak_1565_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1571_, lean_object* v_allowTrailingLinebreak_1572_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1573_; lean_object* v_res_1574_; 
v_allowTrailingLinebreak_boxed_1573_ = lean_unbox(v_allowTrailingLinebreak_1572_);
v_res_1574_ = l_Lake_Toml_sepByLinebreak(v_p_1571_, v_allowTrailingLinebreak_boxed_1573_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1581_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1582_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1583_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1583_, 0, v___x_1581_);
lean_closure_set(v___x_1583_, 1, v_p_1575_);
lean_closure_set(v___x_1583_, 2, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1585_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1583_, v___x_1584_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1593_, uint8_t v_allowTrailingLinebreak_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1593_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1601_, lean_object* v_allowTrailingLinebreak_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1608_; lean_object* v_res_1609_; 
v_allowTrailingLinebreak_boxed_1608_ = lean_unbox(v_allowTrailingLinebreak_1602_);
v_res_1609_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1601_, v_allowTrailingLinebreak_boxed_1608_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1616_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1617_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1618_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1618_, 0, v___x_1616_);
lean_closure_set(v___x_1618_, 1, v_p_1610_);
lean_closure_set(v___x_1618_, 2, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1620_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1618_, v___x_1619_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1628_, uint8_t v_allowTrailingLinebreak_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1628_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1636_, lean_object* v_allowTrailingLinebreak_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1643_; lean_object* v_res_1644_; 
v_allowTrailingLinebreak_boxed_1643_ = lean_unbox(v_allowTrailingLinebreak_1637_);
v_res_1644_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1636_, v_allowTrailingLinebreak_boxed_1643_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1645_, uint8_t v_allowTrailingLinebreak_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_p_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1647_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1648_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1649_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1647_, v_p_1645_, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1651_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1649_, v___x_1650_, v_allowTrailingLinebreak_1646_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1652_, lean_object* v_allowTrailingLinebreak_1653_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1654_; lean_object* v_res_1655_; 
v_allowTrailingLinebreak_boxed_1654_ = lean_unbox(v_allowTrailingLinebreak_1653_);
v_res_1655_ = l_Lake_Toml_sepBy1Linebreak(v_p_1652_, v_allowTrailingLinebreak_boxed_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1656_, lean_object* v_c_1657_, lean_object* v_s_1658_){
_start:
{
lean_object* v_toCacheableParserContext_1659_; lean_object* v_quotDepth_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_toCacheableParserContext_1659_ = lean_ctor_get(v_c_1657_, 2);
v_quotDepth_1660_ = lean_ctor_get(v_toCacheableParserContext_1659_, 1);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_nat_dec_lt(v___x_1661_, v_quotDepth_1660_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_apply_2(v_p_1656_, v_c_1657_, v_s_1658_);
return v___x_1663_;
}
else
{
lean_dec_ref(v_c_1657_);
lean_dec_ref(v_p_1656_);
return v_s_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1670_; 
lean_inc(v_a_1668_);
lean_inc_ref(v_a_1667_);
lean_inc(v_a_1666_);
lean_inc_ref(v_a_1665_);
v___x_1670_ = lean_apply_5(v_p_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, lean_box(0));
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
lean_inc(v_a_1682_);
lean_inc_ref(v_a_1681_);
lean_inc(v_a_1680_);
lean_inc_ref(v_a_1679_);
v___x_1684_ = lean_apply_5(v_p_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, lean_box(0));
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1692_){
_start:
{
lean_object* v_info_1693_; lean_object* v_fn_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_info_1693_ = lean_ctor_get(v_p_1692_, 0);
v_fn_1694_ = lean_ctor_get(v_p_1692_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_p_1692_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_p_1692_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_fn_1694_);
lean_inc(v_info_1693_);
lean_dec(v_p_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1698_, 0, v_fn_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_info_1693_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
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
