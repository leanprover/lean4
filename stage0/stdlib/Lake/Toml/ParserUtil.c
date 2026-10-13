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
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object*, lean_object*);
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
v___x_55_ = l_instBEqOption_beq___redArg(v___x_53_, v_errorMsg_52_, v___x_54_);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(lean_object* v_x_65_, lean_object* v_x_66_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_x_73_, v_x_74_);
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
v___x_86_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_84_, v___x_85_);
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
v___x_99_ = l_instBEqOption_beq___redArg(v___x_97_, v_errorMsg_96_, v___x_98_);
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
v___x_158_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_156_, v___x_157_);
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
v___x_203_ = lean_box(0);
v___x_204_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_202_, v___x_203_);
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
v___x_239_ = lean_box(0);
v___x_240_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_238_, v___x_239_);
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
v___x_352_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_350_, v___x_351_);
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
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_404_ = lean_box(0);
v___x_405_ = l_Lean_Syntax_Traverser_left(v_stxTrav_395_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_leadWord_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_stack_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*3, v_leadWordIdent_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*3 + 1, v_isUngrouped_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*3 + 2, v_mustBeGrouped_399_);
v___x_407_ = v_reuseFailAlloc_410_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_st_ref_put(v___y_392_, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_404_);
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
v___x_427_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_450_; lean_object* v_toCold_451_; lean_object* v_env_452_; lean_object* v_options_453_; uint8_t v___x_454_; lean_object* v_env_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_450_ = lean_st_ref_get(v___y_448_);
v_toCold_451_ = lean_ctor_get(v___y_447_, 0);
v_env_452_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_452_);
lean_dec(v___x_450_);
v_options_453_ = lean_ctor_get(v_toCold_451_, 2);
v___x_454_ = 0;
v_env_455_ = l_Lean_Environment_setRecordingDeps(v_env_452_, v___x_454_);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_453_);
v___x_458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_458_, 0, v_env_455_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set(v___x_458_, 3, v_options_453_);
v___x_459_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_msgData_446_);
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
v_ref_475_ = lean_ctor_get(v___y_472_, 2);
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
lean_object* v___x_481_; lean_object* v_traceState_482_; lean_object* v_env_483_; lean_object* v_nextMacroScope_484_; lean_object* v_ngen_485_; lean_object* v_auxDeclNGen_486_; lean_object* v_cache_487_; lean_object* v_recordedDeps_488_; lean_object* v_messages_489_; lean_object* v_infoState_490_; lean_object* v_snapshotTasks_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_521_; 
v___x_481_ = lean_st_ref_take(v___y_473_);
v_traceState_482_ = lean_ctor_get(v___x_481_, 4);
v_env_483_ = lean_ctor_get(v___x_481_, 0);
v_nextMacroScope_484_ = lean_ctor_get(v___x_481_, 1);
v_ngen_485_ = lean_ctor_get(v___x_481_, 2);
v_auxDeclNGen_486_ = lean_ctor_get(v___x_481_, 3);
v_cache_487_ = lean_ctor_get(v___x_481_, 5);
v_recordedDeps_488_ = lean_ctor_get(v___x_481_, 6);
v_messages_489_ = lean_ctor_get(v___x_481_, 7);
v_infoState_490_ = lean_ctor_get(v___x_481_, 8);
v_snapshotTasks_491_ = lean_ctor_get(v___x_481_, 9);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_521_ == 0)
{
v___x_493_ = v___x_481_;
v_isShared_494_ = v_isSharedCheck_521_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_snapshotTasks_491_);
lean_inc(v_infoState_490_);
lean_inc(v_messages_489_);
lean_inc(v_recordedDeps_488_);
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
lean_object* v___x_500_; lean_object* v___x_501_; double v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_500_ = lean_box(0);
v___x_501_ = lean_box(0);
v___x_502_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_503_ = 0;
v___x_504_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_505_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_505_, 0, v_cls_470_);
lean_ctor_set(v___x_505_, 1, v___x_501_);
lean_ctor_set(v___x_505_, 2, v___x_504_);
lean_ctor_set_float(v___x_505_, sizeof(void*)*3, v___x_502_);
lean_ctor_set_float(v___x_505_, sizeof(void*)*3 + 8, v___x_502_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*3 + 16, v___x_503_);
v___x_506_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_507_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v_a_477_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
lean_inc(v_ref_475_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_ref_475_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_PersistentArray_push___redArg(v_traces_496_, v___x_508_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_509_);
v___x_511_ = v___x_498_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_509_);
lean_ctor_set_uint64(v_reuseFailAlloc_519_, sizeof(void*)*1, v_tid_495_);
v___x_511_ = v_reuseFailAlloc_519_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v___x_511_);
v___x_513_ = v___x_493_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_env_483_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_nextMacroScope_484_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_ngen_485_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_auxDeclNGen_486_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v_cache_487_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_recordedDeps_488_);
lean_ctor_set(v_reuseFailAlloc_518_, 7, v_messages_489_);
lean_ctor_set(v_reuseFailAlloc_518_, 8, v_infoState_490_);
lean_ctor_set(v_reuseFailAlloc_518_, 9, v_snapshotTasks_491_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_st_ref_put(v___y_473_, v___x_513_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_500_);
v___x_516_ = v___x_479_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_500_);
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
lean_dec_ref_known(v_a_554_, 2);
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
lean_dec_ref_known(v___x_561_, 1);
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
lean_object* v_toCold_563_; lean_object* v_options_564_; uint8_t v_hasTrace_565_; 
v_toCold_563_ = lean_ctor_get(v_a_550_, 0);
v_options_564_ = lean_ctor_get(v_toCold_563_, 2);
v_hasTrace_565_ = lean_ctor_get_uint8(v_options_564_, sizeof(void*)*1);
if (v_hasTrace_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_a_554_);
v___x_566_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_566_;
}
else
{
lean_object* v_inheritedTraceOptions_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_inheritedTraceOptions_567_ = lean_ctor_get(v_toCold_563_, 11);
v___x_568_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_569_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_567_, v_options_564_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v_a_554_);
v___x_571_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_572_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_573_ = lean_box(0);
v___x_574_ = 0;
v___x_575_ = l_Lean_Syntax_formatStx(v_a_554_, v___x_573_, v___x_574_);
v___x_576_ = l_Lean_MessageData_ofFormat(v___x_575_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_572_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_568_, v___x_579_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; 
lean_dec_ref_known(v___x_580_, 1);
v___x_581_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_581_;
}
else
{
return v___x_580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lake_Toml_atom_formatter___redArg(v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lake_Toml_atom_formatter___redArg(v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lake_Toml_atom_formatter(v_x_596_, v_x_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_x_597_);
lean_dec_ref(v_x_596_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_604_, lean_object* v_msg_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_604_, v_msg_605_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_612_, lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_612_, v_msg_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_623_);
lean_dec(v_a_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_629_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_634_, v_x_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_x_635_);
lean_dec_ref(v_x_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_642_, lean_object* v_expected_643_, lean_object* v_trailingFn_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_box_uint32(v_c_642_);
v___x_646_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_646_, 0, v___x_645_);
lean_closure_set(v___x_646_, 1, v_expected_643_);
v___x_647_ = l_Lake_Toml_atom(v___x_646_, v_trailingFn_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_648_, lean_object* v_expected_649_, lean_object* v_trailingFn_650_){
_start:
{
uint32_t v_c_boxed_651_; lean_object* v_res_652_; 
v_c_boxed_651_ = lean_unbox_uint32(v_c_648_);
lean_dec(v_c_648_);
v_res_652_ = l_Lake_Toml_chAtom(v_c_boxed_651_, v_expected_649_, v_trailingFn_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
uint8_t v___x_659_; lean_object* v___x_660_; 
v___x_659_ = 0;
v___x_660_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_653_, v___x_659_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
uint32_t v_c_boxed_667_; lean_object* v_res_668_; 
v_c_boxed_667_ = lean_unbox_uint32(v_c_661_);
lean_dec(v_c_661_);
v_res_668_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_667_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_669_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
uint32_t v_c_boxed_686_; lean_object* v_res_687_; 
v_c_boxed_686_ = lean_unbox_uint32(v_c_678_);
lean_dec(v_c_678_);
v_res_687_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_686_, v_x_679_, v_x_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec_ref(v_x_680_);
lean_dec(v_x_679_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_691_);
lean_dec(v_a_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_698_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
uint32_t v_x_19__boxed_711_; lean_object* v_res_712_; 
v_x_19__boxed_711_ = lean_unbox_uint32(v_x_703_);
lean_dec(v_x_703_);
v_res_712_ = l_Lake_Toml_chAtom_parenthesizer(v_x_19__boxed_711_, v_x_704_, v_x_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec_ref(v_x_705_);
lean_dec(v_x_704_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_713_, lean_object* v_expected_714_, lean_object* v_trailingFn_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_str_720_; lean_object* v_startInclusive_721_; lean_object* v_endExclusive_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_string_utf8_byte_size(v_s_713_);
v___x_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_718_, 0, v_s_713_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
v___x_719_ = l_String_Slice_trimAscii(v___x_718_);
v_str_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_str_720_);
v_startInclusive_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_startInclusive_721_);
v_endExclusive_722_ = lean_ctor_get(v___x_719_, 2);
lean_inc(v_endExclusive_722_);
lean_dec_ref(v___x_719_);
v___x_723_ = lean_string_utf8_extract_fast(v_str_720_, v_startInclusive_721_, v_endExclusive_722_);
lean_dec(v_endExclusive_722_);
lean_dec(v_startInclusive_721_);
lean_dec_ref(v_str_720_);
v___x_724_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_724_, 0, v___x_723_);
lean_closure_set(v___x_724_, 1, v_expected_714_);
v___x_725_ = l_Lake_Toml_atom(v___x_724_, v_trailingFn_715_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_740_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lake_Toml_strAtom_formatter(v_s_749_, v_x_750_, v_x_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec_ref(v_x_751_);
lean_dec(v_x_750_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_761_);
lean_dec(v_a_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_768_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lake_Toml_strAtom_parenthesizer(v_x_773_, v_x_774_, v_x_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec_ref(v_x_775_);
lean_dec(v_x_774_);
lean_dec_ref(v_x_773_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_782_, lean_object* v_startPos_783_, lean_object* v_trailingFn_784_, lean_object* v_c_785_, lean_object* v_s_786_){
_start:
{
lean_object* v_toInputContext_787_; lean_object* v_pos_788_; lean_object* v_inputString_789_; lean_object* v_endPos_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_808_; 
v_toInputContext_787_ = lean_ctor_get(v_c_785_, 0);
lean_inc_ref(v_toInputContext_787_);
v_pos_788_ = lean_ctor_get(v_s_786_, 2);
lean_inc(v_pos_788_);
v_inputString_789_ = lean_ctor_get(v_toInputContext_787_, 0);
v_endPos_790_ = lean_ctor_get(v_toInputContext_787_, 3);
v_isSharedCheck_808_ = !lean_is_exclusive(v_toInputContext_787_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_809_ = lean_ctor_get(v_toInputContext_787_, 2);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_toInputContext_787_, 1);
lean_dec(v_unused_810_);
v___x_792_ = v_toInputContext_787_;
v_isShared_793_ = v_isSharedCheck_808_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_endPos_790_);
lean_inc(v_inputString_789_);
lean_dec(v_toInputContext_787_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_808_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_leading_794_; lean_object* v_s_795_; lean_object* v_pos_796_; lean_object* v_val_797_; lean_object* v___y_799_; uint8_t v___x_805_; 
lean_inc(v_startPos_783_);
v_leading_794_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_785_, v_startPos_783_);
v_s_795_ = lean_apply_2(v_trailingFn_784_, v_c_785_, v_s_786_);
v_pos_796_ = lean_ctor_get(v_s_795_, 2);
lean_inc(v_pos_796_);
v_val_797_ = lean_string_utf8_extract(v_inputString_789_, v_startPos_783_, v_pos_788_);
v___x_805_ = lean_nat_dec_le(v_pos_796_, v_endPos_790_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec(v_pos_796_);
lean_inc(v_pos_788_);
v___x_806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_806_, 0, v_inputString_789_);
lean_ctor_set(v___x_806_, 1, v_pos_788_);
lean_ctor_set(v___x_806_, 2, v_endPos_790_);
v___y_799_ = v___x_806_;
goto v___jp_798_;
}
else
{
lean_object* v___x_807_; 
lean_dec(v_endPos_790_);
lean_inc(v_pos_788_);
v___x_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_807_, 0, v_inputString_789_);
lean_ctor_set(v___x_807_, 1, v_pos_788_);
lean_ctor_set(v___x_807_, 2, v_pos_796_);
v___y_799_ = v___x_807_;
goto v___jp_798_;
}
v___jp_798_:
{
lean_object* v_info_801_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 3, v_pos_788_);
lean_ctor_set(v___x_792_, 2, v___y_799_);
lean_ctor_set(v___x_792_, 1, v_startPos_783_);
lean_ctor_set(v___x_792_, 0, v_leading_794_);
v_info_801_ = v___x_792_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_leading_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_startPos_783_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v___y_799_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_pos_788_);
v_info_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = l_Lean_Syntax_mkLit(v_kind_782_, v_val_797_, v_info_801_);
v___x_803_ = l_Lean_Parser_ParserState_pushSyntax(v_s_795_, v___x_802_);
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_811_, lean_object* v_p_812_, lean_object* v_trailingFn_813_, lean_object* v_c_814_, lean_object* v_s_815_){
_start:
{
lean_object* v_pos_816_; lean_object* v_s_817_; lean_object* v_errorMsg_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_pos_816_ = lean_ctor_get(v_s_815_, 2);
lean_inc(v_pos_816_);
lean_inc_ref(v_c_814_);
v_s_817_ = lean_apply_2(v_p_812_, v_c_814_, v_s_815_);
v_errorMsg_818_ = lean_ctor_get(v_s_817_, 4);
lean_inc(v_errorMsg_818_);
v___x_819_ = lean_box(0);
v___x_820_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_818_, v___x_819_);
lean_dec(v_errorMsg_818_);
if (v___x_820_ == 0)
{
lean_dec(v_pos_816_);
lean_dec_ref(v_c_814_);
lean_dec_ref(v_trailingFn_813_);
lean_dec(v_kind_811_);
return v_s_817_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = l_Lake_Toml_pushLit(v_kind_811_, v_pos_816_, v_trailingFn_813_, v_c_814_, v_s_817_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_822_, lean_object* v_p_823_, lean_object* v_trailingFn_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_826_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_826_, 0, v_kind_822_);
lean_closure_set(v___x_826_, 1, v_p_823_);
lean_closure_set(v___x_826_, 2, v_trailingFn_824_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lake_Toml_lit_formatter___redArg(v_kind_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_842_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lake_Toml_lit_formatter(v_kind_851_, v_x_852_, v_x_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec_ref(v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_863_);
lean_dec(v_a_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_870_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lake_Toml_lit_parenthesizer(v_x_875_, v_x_876_, v_x_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec_ref(v_x_877_);
lean_dec_ref(v_x_876_);
lean_dec(v_x_875_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_898_, lean_object* v_kind_899_, uint8_t v_anonymous_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___f_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_inc(v_kind_899_);
v___f_906_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_906_, 0, v_kind_899_);
v___x_907_ = 0;
v___x_908_ = lean_box(v_anonymous_900_);
v___x_909_ = lean_box(v___x_907_);
v___x_910_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_910_, 0, v_name_898_);
lean_closure_set(v___x_910_, 1, v_kind_899_);
lean_closure_set(v___x_910_, 2, v___x_908_);
lean_closure_set(v___x_910_, 3, v___x_909_);
v___x_911_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_910_, v___f_906_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_912_, lean_object* v_kind_913_, lean_object* v_anonymous_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_anonymous_boxed_920_; lean_object* v_res_921_; 
v_anonymous_boxed_920_ = lean_unbox(v_anonymous_914_);
v_res_921_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_912_, v_kind_913_, v_anonymous_boxed_920_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_922_, lean_object* v_kind_923_, lean_object* v_p_924_, lean_object* v_trailingFn_925_, uint8_t v_anonymous_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_922_, v_kind_923_, v_anonymous_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_933_, lean_object* v_kind_934_, lean_object* v_p_935_, lean_object* v_trailingFn_936_, lean_object* v_anonymous_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
uint8_t v_anonymous_boxed_943_; lean_object* v_res_944_; 
v_anonymous_boxed_943_ = lean_unbox(v_anonymous_937_);
v_res_944_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_933_, v_kind_934_, v_p_935_, v_trailingFn_936_, v_anonymous_boxed_943_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec_ref(v_trailingFn_936_);
lean_dec_ref(v_p_935_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_946_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_958_, lean_object* v_kind_959_, uint8_t v_anonymous_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___f_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___f_966_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_967_ = 0;
v___x_968_ = lean_box(v_anonymous_960_);
v___x_969_ = lean_box(v___x_967_);
v___x_970_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_970_, 0, v_name_958_);
lean_closure_set(v___x_970_, 1, v_kind_959_);
lean_closure_set(v___x_970_, 2, v___x_968_);
lean_closure_set(v___x_970_, 3, v___x_969_);
v___x_971_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_970_, v___f_966_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_972_, lean_object* v_kind_973_, lean_object* v_anonymous_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
uint8_t v_anonymous_boxed_980_; lean_object* v_res_981_; 
v_anonymous_boxed_980_ = lean_unbox(v_anonymous_974_);
v_res_981_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_972_, v_kind_973_, v_anonymous_boxed_980_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_982_, lean_object* v_kind_983_, lean_object* v_p_984_, lean_object* v_trailingFn_985_, uint8_t v_anonymous_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_982_, v_kind_983_, v_anonymous_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_993_, lean_object* v_kind_994_, lean_object* v_p_995_, lean_object* v_trailingFn_996_, lean_object* v_anonymous_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
uint8_t v_anonymous_boxed_1003_; lean_object* v_res_1004_; 
v_anonymous_boxed_1003_ = lean_unbox(v_anonymous_997_);
v_res_1004_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_993_, v_kind_994_, v_p_995_, v_trailingFn_996_, v_anonymous_boxed_1003_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_trailingFn_996_);
lean_dec_ref(v_p_995_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1005_, lean_object* v_kind_1006_, lean_object* v_p_1007_, lean_object* v_trailingFn_1008_, uint8_t v_anonymous_1009_){
_start:
{
uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = 0;
lean_inc(v_kind_1006_);
v___x_1011_ = l_Lean_Parser_mkAntiquot(v_name_1005_, v_kind_1006_, v_anonymous_1009_, v___x_1010_);
v___x_1012_ = l_Lake_Toml_lit(v_kind_1006_, v_p_1007_, v_trailingFn_1008_);
v___x_1013_ = l_Lean_Parser_withAntiquot(v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1014_, lean_object* v_kind_1015_, lean_object* v_p_1016_, lean_object* v_trailingFn_1017_, lean_object* v_anonymous_1018_){
_start:
{
uint8_t v_anonymous_boxed_1019_; lean_object* v_res_1020_; 
v_anonymous_boxed_1019_ = lean_unbox(v_anonymous_1018_);
v_res_1020_ = l_Lake_Toml_litWithAntiquot(v_name_1014_, v_kind_1015_, v_p_1016_, v_trailingFn_1017_, v_anonymous_boxed_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = l_Lean_Parser_epsilonInfo;
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_fn_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lake_Toml_epsilon_formatter(v_x_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec_ref(v_x_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec_ref(v_x_1055_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1062_, lean_object* v_x_1063_){
_start:
{
switch(lean_obj_tag(v_x_1063_))
{
case 2:
{
lean_object* v_info_1064_; lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
v_info_1064_ = lean_ctor_get(v_x_1063_, 0);
v_val_1065_ = lean_ctor_get(v_x_1063_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1067_ = v_x_1063_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_inc(v_info_1064_);
lean_dec(v_x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_apply_1(v_f_1062_, v_info_1064_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_val_1065_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
case 3:
{
lean_object* v_info_1074_; lean_object* v_rawVal_1075_; lean_object* v_val_1076_; lean_object* v_preresolved_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_info_1074_ = lean_ctor_get(v_x_1063_, 0);
v_rawVal_1075_ = lean_ctor_get(v_x_1063_, 1);
v_val_1076_ = lean_ctor_get(v_x_1063_, 2);
v_preresolved_1077_ = lean_ctor_get(v_x_1063_, 3);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1079_ = v_x_1063_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_preresolved_1077_);
lean_inc(v_val_1076_);
lean_inc(v_rawVal_1075_);
lean_inc(v_info_1074_);
lean_dec(v_x_1063_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_apply_1(v_f_1062_, v_info_1074_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_rawVal_1075_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_val_1076_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_preresolved_1077_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
case 1:
{
lean_object* v_info_1086_; lean_object* v_kind_1087_; lean_object* v_args_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_info_1086_ = lean_ctor_get(v_x_1063_, 0);
v_kind_1087_ = lean_ctor_get(v_x_1063_, 1);
v_args_1088_ = lean_ctor_get(v_x_1063_, 2);
v___x_1089_ = lean_array_get_size(v_args_1088_);
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_nat_sub(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_nat_dec_lt(v___x_1091_, v___x_1089_);
if (v___x_1092_ == 0)
{
lean_dec(v___x_1091_);
lean_dec_ref(v_f_1062_);
return v_x_1063_;
}
else
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1104_; 
lean_inc_ref(v_args_1088_);
lean_inc(v_kind_1087_);
lean_inc(v_info_1086_);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; 
v_unused_1105_ = lean_ctor_get(v_x_1063_, 2);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_x_1063_, 1);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_x_1063_, 0);
lean_dec(v_unused_1107_);
v___x_1094_ = v_x_1063_;
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v_x_1063_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_v_1096_; lean_object* v___x_1097_; lean_object* v_xs_x27_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v_v_1096_ = lean_array_fget(v_args_1088_, v___x_1091_);
v___x_1097_ = lean_box(0);
v_xs_x27_1098_ = lean_array_fset(v_args_1088_, v___x_1091_, v___x_1097_);
v___x_1099_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1062_, v_v_1096_);
v___x_1100_ = lean_array_fset(v_xs_x27_1098_, v___x_1091_, v___x_1099_);
lean_dec(v___x_1091_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1100_);
v___x_1102_ = v___x_1094_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_info_1086_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_kind_1087_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1062_);
return v_x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v_trailing_1110_; lean_object* v_leading_1111_; lean_object* v_pos_1112_; lean_object* v_endPos_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1130_; 
v_trailing_1110_ = lean_ctor_get(v_x_1109_, 2);
v_leading_1111_ = lean_ctor_get(v_x_1109_, 0);
v_pos_1112_ = lean_ctor_get(v_x_1109_, 1);
v_endPos_1113_ = lean_ctor_get(v_x_1109_, 3);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1115_ = v_x_1109_;
v_isShared_1116_ = v_isSharedCheck_1130_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_endPos_1113_);
lean_inc(v_trailing_1110_);
lean_inc(v_pos_1112_);
lean_inc(v_leading_1111_);
lean_dec(v_x_1109_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1130_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_str_1117_; lean_object* v_startPos_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v_str_1117_ = lean_ctor_get(v_trailing_1110_, 0);
v_startPos_1118_ = lean_ctor_get(v_trailing_1110_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_trailing_1110_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_trailing_1110_, 2);
lean_dec(v_unused_1129_);
v___x_1120_ = v_trailing_1110_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_startPos_1118_);
lean_inc(v_str_1117_);
lean_dec(v_trailing_1110_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 2, v_stopPos_1108_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_str_1117_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_startPos_1118_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_stopPos_1108_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 2, v___x_1123_);
v___x_1125_ = v___x_1115_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_leading_1111_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_pos_1112_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_endPos_1113_);
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
}
else
{
lean_dec(v_stopPos_1108_);
return v_x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1131_, lean_object* v_x_1132_){
_start:
{
switch(lean_obj_tag(v_x_1132_))
{
case 2:
{
lean_object* v_info_1133_; lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_info_1133_ = lean_ctor_get(v_x_1132_, 0);
v_val_1134_ = lean_ctor_get(v_x_1132_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v_x_1132_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_inc(v_info_1133_);
lean_dec(v_x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1131_, v_info_1133_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_val_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
case 3:
{
lean_object* v_info_1143_; lean_object* v_rawVal_1144_; lean_object* v_val_1145_; lean_object* v_preresolved_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_info_1143_ = lean_ctor_get(v_x_1132_, 0);
v_rawVal_1144_ = lean_ctor_get(v_x_1132_, 1);
v_val_1145_ = lean_ctor_get(v_x_1132_, 2);
v_preresolved_1146_ = lean_ctor_get(v_x_1132_, 3);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v_x_1132_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_preresolved_1146_);
lean_inc(v_val_1145_);
lean_inc(v_rawVal_1144_);
lean_inc(v_info_1143_);
lean_dec(v_x_1132_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1131_, v_info_1143_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_rawVal_1144_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_val_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_preresolved_1146_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
case 1:
{
lean_object* v_info_1155_; lean_object* v_kind_1156_; lean_object* v_args_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_info_1155_ = lean_ctor_get(v_x_1132_, 0);
v_kind_1156_ = lean_ctor_get(v_x_1132_, 1);
v_args_1157_ = lean_ctor_get(v_x_1132_, 2);
v___x_1158_ = lean_array_get_size(v_args_1157_);
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_sub(v___x_1158_, v___x_1159_);
v___x_1161_ = lean_nat_dec_lt(v___x_1160_, v___x_1158_);
if (v___x_1161_ == 0)
{
lean_dec(v___x_1160_);
lean_dec(v_stopPos_1131_);
return v_x_1132_;
}
else
{
lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1173_; 
lean_inc_ref(v_args_1157_);
lean_inc(v_kind_1156_);
lean_inc(v_info_1155_);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1174_ = lean_ctor_get(v_x_1132_, 2);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_x_1132_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_x_1132_, 0);
lean_dec(v_unused_1176_);
v___x_1163_ = v_x_1132_;
v_isShared_1164_ = v_isSharedCheck_1173_;
goto v_resetjp_1162_;
}
else
{
lean_dec(v_x_1132_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1173_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_v_1165_; lean_object* v___x_1166_; lean_object* v_xs_x27_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v_v_1165_ = lean_array_fget(v_args_1157_, v___x_1160_);
v___x_1166_ = lean_box(0);
v_xs_x27_1167_ = lean_array_fset(v_args_1157_, v___x_1160_, v___x_1166_);
v___x_1168_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1131_, v_v_1165_);
v___x_1169_ = lean_array_fset(v_xs_x27_1167_, v___x_1160_, v___x_1168_);
lean_dec(v___x_1160_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 2, v___x_1169_);
v___x_1171_ = v___x_1163_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_info_1155_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_kind_1156_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1131_);
return v_x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1177_, lean_object* v_c_1178_, lean_object* v_s_1179_){
_start:
{
lean_object* v_s_1180_; lean_object* v_stxStack_1181_; lean_object* v_pos_1182_; lean_object* v_tail_1183_; lean_object* v_s_1184_; lean_object* v_tail_1185_; lean_object* v___x_1186_; 
v_s_1180_ = lean_apply_2(v_p_1177_, v_c_1178_, v_s_1179_);
v_stxStack_1181_ = lean_ctor_get(v_s_1180_, 0);
lean_inc_ref(v_stxStack_1181_);
v_pos_1182_ = lean_ctor_get(v_s_1180_, 2);
lean_inc(v_pos_1182_);
v_tail_1183_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1181_);
lean_dec_ref(v_stxStack_1181_);
v_s_1184_ = l_Lean_Parser_ParserState_popSyntax(v_s_1180_);
v_tail_1185_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1182_, v_tail_1183_);
v___x_1186_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1184_, v_tail_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lake_Toml_trailing_formatter(v_p_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec_ref(v_p_1198_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lake_Toml_trailing_parenthesizer(v_p_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v_p_1216_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1224_, 0, v_p_1223_);
v___x_1225_ = l_Lean_Parser_epsilonInfo;
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_p_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1235_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1231_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = l_Lean_Syntax_getKind(v_a_1236_);
v___x_1238_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1237_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lake_Toml_dynamicNode_formatter(v_x_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec_ref(v_x_1252_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v_stxTrav_1262_; lean_object* v_cur_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_st_ref_get(v___y_1259_);
v_stxTrav_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_ref(v_stxTrav_1262_);
lean_dec(v___x_1261_);
v_cur_1263_ = lean_ctor_get(v_stxTrav_1262_, 0);
lean_inc(v_cur_1263_);
lean_dec_ref(v_stxTrav_1262_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_cur_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1265_);
lean_dec(v___y_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1269_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1281_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = l_Lean_Syntax_getKind(v_a_1286_);
v___x_1288_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1287_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_x_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_fn_1315_; lean_object* v___x_1316_; 
lean_inc_ref(v_f_1309_);
v___x_1312_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1312_, 0, v_f_1309_);
v___x_1313_ = l_Lake_Toml_dynamicNode(v___x_1312_);
v___x_1314_ = lean_apply_1(v_f_1309_, v___x_1313_);
v_fn_1315_ = lean_ctor_get(v___x_1314_, 1);
lean_inc_ref(v_fn_1315_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = lean_apply_2(v_fn_1315_, v_a_1310_, v_a_1311_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lake_Toml_recNode_formatter(v_f_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec_ref(v_f_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lake_Toml_recNode_parenthesizer(v_f_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec_ref(v_f_1362_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1370_, 0, v_f_1369_);
v___x_1371_ = l_Lake_Toml_dynamicNode(v___x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1372_, lean_object* v_kind_1373_, lean_object* v_f_1374_, uint8_t v_anonymous_1375_, lean_object* v_p_1376_){
_start:
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1377_ = 1;
lean_inc(v_kind_1373_);
v___x_1378_ = l_Lean_Parser_mkAntiquot(v_name_1372_, v_kind_1373_, v_anonymous_1375_, v___x_1377_);
v___x_1379_ = lean_apply_1(v_f_1374_, v_p_1376_);
v___x_1380_ = l_Lean_Parser_withAntiquot(v___x_1378_, v___x_1379_);
v___x_1381_ = l_Lean_Parser_withCache(v_kind_1373_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1382_, lean_object* v_kind_1383_, lean_object* v_f_1384_, lean_object* v_anonymous_1385_, lean_object* v_p_1386_){
_start:
{
uint8_t v_anonymous_boxed_1387_; lean_object* v_res_1388_; 
v_anonymous_boxed_1387_ = lean_unbox(v_anonymous_1385_);
v_res_1388_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1382_, v_kind_1383_, v_f_1384_, v_anonymous_boxed_1387_, v_p_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1389_, lean_object* v_kind_1390_, lean_object* v_f_1391_, uint8_t v_anonymous_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1398_ = 1;
v___x_1399_ = lean_box(v_anonymous_1392_);
v___x_1400_ = lean_box(v___x_1398_);
lean_inc(v_kind_1390_);
lean_inc_ref(v_name_1389_);
v___x_1401_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1401_, 0, v_name_1389_);
lean_closure_set(v___x_1401_, 1, v_kind_1390_);
lean_closure_set(v___x_1401_, 2, v___x_1399_);
lean_closure_set(v___x_1401_, 3, v___x_1400_);
v___x_1402_ = lean_box(v_anonymous_1392_);
v___x_1403_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1403_, 0, v_name_1389_);
lean_closure_set(v___x_1403_, 1, v_kind_1390_);
lean_closure_set(v___x_1403_, 2, v_f_1391_);
lean_closure_set(v___x_1403_, 3, v___x_1402_);
v___x_1404_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1404_, 0, v___x_1403_);
v___x_1405_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1401_, v___x_1404_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1406_, lean_object* v_kind_1407_, lean_object* v_f_1408_, lean_object* v_anonymous_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
uint8_t v_anonymous_boxed_1415_; lean_object* v_res_1416_; 
v_anonymous_boxed_1415_ = lean_unbox(v_anonymous_1409_);
v_res_1416_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1406_, v_kind_1407_, v_f_1408_, v_anonymous_boxed_1415_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1417_, lean_object* v_kind_1418_, lean_object* v_f_1419_, uint8_t v_anonymous_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1426_ = 1;
v___x_1427_ = lean_box(v_anonymous_1420_);
v___x_1428_ = lean_box(v___x_1426_);
lean_inc(v_kind_1418_);
lean_inc_ref(v_name_1417_);
v___x_1429_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1429_, 0, v_name_1417_);
lean_closure_set(v___x_1429_, 1, v_kind_1418_);
lean_closure_set(v___x_1429_, 2, v___x_1427_);
lean_closure_set(v___x_1429_, 3, v___x_1428_);
v___x_1430_ = lean_box(v_anonymous_1420_);
v___x_1431_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1431_, 0, v_name_1417_);
lean_closure_set(v___x_1431_, 1, v_kind_1418_);
lean_closure_set(v___x_1431_, 2, v_f_1419_);
lean_closure_set(v___x_1431_, 3, v___x_1430_);
v___x_1432_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1432_, 0, v___x_1431_);
v___x_1433_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1429_, v___x_1432_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1434_, lean_object* v_kind_1435_, lean_object* v_f_1436_, lean_object* v_anonymous_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
uint8_t v_anonymous_boxed_1443_; lean_object* v_res_1444_; 
v_anonymous_boxed_1443_ = lean_unbox(v_anonymous_1437_);
v_res_1444_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1434_, v_kind_1435_, v_f_1436_, v_anonymous_boxed_1443_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1445_, lean_object* v_kind_1446_, lean_object* v_f_1447_, uint8_t v_anonymous_1448_){
_start:
{
uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1449_ = 1;
lean_inc_n(v_kind_1446_, 2);
lean_inc_ref(v_name_1445_);
v___x_1450_ = l_Lean_Parser_mkAntiquot(v_name_1445_, v_kind_1446_, v_anonymous_1448_, v___x_1449_);
v___x_1451_ = lean_box(v_anonymous_1448_);
v___x_1452_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1452_, 0, v_name_1445_);
lean_closure_set(v___x_1452_, 1, v_kind_1446_);
lean_closure_set(v___x_1452_, 2, v_f_1447_);
lean_closure_set(v___x_1452_, 3, v___x_1451_);
v___x_1453_ = l_Lake_Toml_recNode(v___x_1452_);
v___x_1454_ = l_Lean_Parser_withAntiquot(v___x_1450_, v___x_1453_);
v___x_1455_ = l_Lean_Parser_withCache(v_kind_1446_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1456_, lean_object* v_kind_1457_, lean_object* v_f_1458_, lean_object* v_anonymous_1459_){
_start:
{
uint8_t v_anonymous_boxed_1460_; lean_object* v_res_1461_; 
v_anonymous_boxed_1460_ = lean_unbox(v_anonymous_1459_);
v_res_1461_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1456_, v_kind_1457_, v_f_1458_, v_anonymous_boxed_1460_);
return v_res_1461_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___f_1469_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1470_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1471_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1471_, 0, v___x_1470_);
lean_closure_set(v___x_1471_, 1, v___f_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1478_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1479_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1480_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1480_, 0, v___x_1478_);
lean_closure_set(v___x_1480_, 1, v_p_1472_);
lean_closure_set(v___x_1480_, 2, v___x_1479_);
v___x_1481_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1482_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1480_, v___x_1481_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1490_, uint8_t v_allowTrailingLinebreak_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1490_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1498_, lean_object* v_allowTrailingLinebreak_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1505_; lean_object* v_res_1506_; 
v_allowTrailingLinebreak_boxed_1505_ = lean_unbox(v_allowTrailingLinebreak_1499_);
v_res_1506_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1498_, v_allowTrailingLinebreak_boxed_1505_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
return v_res_1506_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___f_1510_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1511_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1512_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1512_, 0, v___x_1511_);
lean_closure_set(v___x_1512_, 1, v___f_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1519_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1520_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1521_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1521_, 0, v___x_1519_);
lean_closure_set(v___x_1521_, 1, v_p_1513_);
lean_closure_set(v___x_1521_, 2, v___x_1520_);
v___x_1522_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1523_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1521_, v___x_1522_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1531_, uint8_t v_allowTrailingLinebreak_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1531_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1539_, lean_object* v_allowTrailingLinebreak_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1546_; lean_object* v_res_1547_; 
v_allowTrailingLinebreak_boxed_1546_ = lean_unbox(v_allowTrailingLinebreak_1540_);
v_res_1547_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1539_, v_allowTrailingLinebreak_boxed_1546_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
return v_res_1547_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1549_ = l_Lean_Parser_symbol(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1552_ = l_Lean_Parser_checkLinebreakBefore(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = l_Lean_Parser_pushNone;
v___x_1554_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1555_ = l_Lean_Parser_andthen(v___x_1554_, v___x_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1556_, uint8_t v_allowTrailingLinebreak_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_p_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1558_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1559_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1560_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1558_, v_p_1556_, v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1562_ = l_Lean_Parser_sepByNoAntiquot(v_p_1560_, v___x_1561_, v_allowTrailingLinebreak_1557_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1563_, lean_object* v_allowTrailingLinebreak_1564_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1565_; lean_object* v_res_1566_; 
v_allowTrailingLinebreak_boxed_1565_ = lean_unbox(v_allowTrailingLinebreak_1564_);
v_res_1566_ = l_Lake_Toml_sepByLinebreak(v_p_1563_, v_allowTrailingLinebreak_boxed_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1573_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1574_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1575_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1575_, 0, v___x_1573_);
lean_closure_set(v___x_1575_, 1, v_p_1567_);
lean_closure_set(v___x_1575_, 2, v___x_1574_);
v___x_1576_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1577_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1575_, v___x_1576_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1585_, uint8_t v_allowTrailingLinebreak_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1585_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1593_, lean_object* v_allowTrailingLinebreak_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1600_; lean_object* v_res_1601_; 
v_allowTrailingLinebreak_boxed_1600_ = lean_unbox(v_allowTrailingLinebreak_1594_);
v_res_1601_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1593_, v_allowTrailingLinebreak_boxed_1600_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1608_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1609_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1610_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1610_, 0, v___x_1608_);
lean_closure_set(v___x_1610_, 1, v_p_1602_);
lean_closure_set(v___x_1610_, 2, v___x_1609_);
v___x_1611_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1612_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1610_, v___x_1611_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1620_, uint8_t v_allowTrailingLinebreak_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1620_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1628_, lean_object* v_allowTrailingLinebreak_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1635_; lean_object* v_res_1636_; 
v_allowTrailingLinebreak_boxed_1635_ = lean_unbox(v_allowTrailingLinebreak_1629_);
v_res_1636_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1628_, v_allowTrailingLinebreak_boxed_1635_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1637_, uint8_t v_allowTrailingLinebreak_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_p_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1639_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1640_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1641_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1639_, v_p_1637_, v___x_1640_);
v___x_1642_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1643_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1641_, v___x_1642_, v_allowTrailingLinebreak_1638_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1644_, lean_object* v_allowTrailingLinebreak_1645_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1646_; lean_object* v_res_1647_; 
v_allowTrailingLinebreak_boxed_1646_ = lean_unbox(v_allowTrailingLinebreak_1645_);
v_res_1647_ = l_Lake_Toml_sepBy1Linebreak(v_p_1644_, v_allowTrailingLinebreak_boxed_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1648_, lean_object* v_c_1649_, lean_object* v_s_1650_){
_start:
{
lean_object* v_toCacheableParserContext_1651_; lean_object* v_quotDepth_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_toCacheableParserContext_1651_ = lean_ctor_get(v_c_1649_, 2);
v_quotDepth_1652_ = lean_ctor_get(v_toCacheableParserContext_1651_, 1);
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = lean_nat_dec_lt(v___x_1653_, v_quotDepth_1652_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_apply_2(v_p_1648_, v_c_1649_, v_s_1650_);
return v___x_1655_;
}
else
{
lean_dec_ref(v_c_1649_);
lean_dec_ref(v_p_1648_);
return v_s_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
lean_inc(v_a_1660_);
lean_inc_ref(v_a_1659_);
lean_inc(v_a_1658_);
lean_inc_ref(v_a_1657_);
v___x_1662_ = lean_apply_5(v_p_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, lean_box(0));
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1676_; 
lean_inc(v_a_1674_);
lean_inc_ref(v_a_1673_);
lean_inc(v_a_1672_);
lean_inc_ref(v_a_1671_);
v___x_1676_ = lean_apply_5(v_p_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, lean_box(0));
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1684_){
_start:
{
lean_object* v_info_1685_; lean_object* v_fn_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_info_1685_ = lean_ctor_get(v_p_1684_, 0);
v_fn_1686_ = lean_ctor_get(v_p_1684_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_p_1684_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v_p_1684_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_fn_1686_);
lean_inc(v_info_1685_);
lean_dec(v_p_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1690_, 0, v_fn_1686_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_info_1685_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
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
