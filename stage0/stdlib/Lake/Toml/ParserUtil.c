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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t l_Lake_Toml_isBinDigit(uint32_t v_c_1_){
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
LEAN_EXPORT void l_Lake_Toml_isBinDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
uint8_t v_res_6_;
v_res_6_ = l_Lake_Toml_isBinDigit(v_c_1_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object* v_c_7_){
_start:
{
uint32_t v_c_boxed_8_; uint8_t v_res_9_; lean_object* v_r_10_; 
v_c_boxed_8_ = lean_unbox_uint32(v_c_7_);
lean_dec(v_c_7_);
v_res_9_ = l_Lake_Toml_isBinDigit(v_c_boxed_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_Lake_Toml_isOctDigit(uint32_t v_c_11_){
_start:
{
uint32_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 48;
v___x_13_ = lean_uint32_dec_le(v___x_12_, v_c_11_);
if (v___x_13_ == 0)
{
return v___x_13_;
}
else
{
uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 55;
v___x_15_ = lean_uint32_dec_le(v_c_11_, v___x_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_isOctDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_11_ = stack[0].m_num;
uint8_t v_res_16_;
v_res_16_ = l_Lake_Toml_isOctDigit(v_c_11_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object* v_c_17_){
_start:
{
uint32_t v_c_boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_c_boxed_18_ = lean_unbox_uint32(v_c_17_);
lean_dec(v_c_17_);
v_res_19_ = l_Lake_Toml_isOctDigit(v_c_boxed_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Lake_Toml_isHexDigit(uint32_t v_c_21_){
_start:
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 48;
v___x_33_ = lean_uint32_dec_le(v___x_32_, v_c_21_);
if (v___x_33_ == 0)
{
goto v___jp_27_;
}
else
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 57;
v___x_35_ = lean_uint32_dec_le(v_c_21_, v___x_34_);
if (v___x_35_ == 0)
{
goto v___jp_27_;
}
else
{
return v___x_35_;
}
}
v___jp_22_:
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 65;
v___x_24_ = lean_uint32_dec_le(v___x_23_, v_c_21_);
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 70;
v___x_26_ = lean_uint32_dec_le(v_c_21_, v___x_25_);
return v___x_26_;
}
}
v___jp_27_:
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 97;
v___x_29_ = lean_uint32_dec_le(v___x_28_, v_c_21_);
if (v___x_29_ == 0)
{
goto v___jp_22_;
}
else
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 102;
v___x_31_ = lean_uint32_dec_le(v_c_21_, v___x_30_);
if (v___x_31_ == 0)
{
goto v___jp_22_;
}
else
{
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_isHexDigit_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_21_ = stack[0].m_num;
uint8_t v_res_36_;
v_res_36_ = l_Lake_Toml_isHexDigit(v_c_21_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object* v_c_37_){
_start:
{
uint32_t v_c_boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_c_boxed_38_ = lean_unbox_uint32(v_c_37_);
lean_dec(v_c_37_);
v_res_39_ = l_Lake_Toml_isHexDigit(v_c_boxed_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg(lean_object* v_s_41_){
_start:
{
lean_inc_ref(v_s_41_);
return v_s_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___redArg___boxed(lean_object* v_s_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_Toml_skipFn___redArg(v_s_42_);
lean_dec_ref(v_s_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn(lean_object* v_x_44_, lean_object* v_s_45_){
_start:
{
lean_inc_ref(v_s_45_);
return v_s_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipFn___boxed(lean_object* v_x_46_, lean_object* v_s_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_Toml_skipFn(v_x_46_, v_s_47_);
lean_dec_ref(v_s_47_);
lean_dec_ref(v_x_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instAndThenParserFn__lake___lam__0(lean_object* v_p_50_, lean_object* v_q_51_, lean_object* v_c_52_, lean_object* v_s_53_){
_start:
{
lean_object* v_s_54_; lean_object* v_errorMsg_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
lean_inc_ref(v_c_52_);
v_s_54_ = lean_apply_2(v_p_50_, v_c_52_, v_s_53_);
v_errorMsg_55_ = lean_ctor_get(v_s_54_, 4);
lean_inc(v_errorMsg_55_);
v___x_56_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_57_ = lean_box(0);
v___x_58_ = l_instBEqOption_beq___redArg(v___x_56_, v_errorMsg_55_, v___x_57_);
if (v___x_58_ == 0)
{
lean_dec_ref(v_c_52_);
lean_dec_ref(v_q_51_);
return v_s_54_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_3(v_q_51_, v___x_59_, v_c_52_, v_s_54_);
return v___x_60_;
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
uint8_t l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(lean_object* v_x_68_, lean_object* v_x_69_){
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
v___x_71_ = 0;
return v___x_71_;
}
}
else
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v_val_74_; uint8_t v___x_75_; 
v_val_73_ = lean_ctor_get(v_x_68_, 0);
v_val_74_ = lean_ctor_get(v_x_69_, 0);
v___x_75_ = l_Lean_Parser_instBEqError_beq(v_val_73_, v_val_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_68_ = stack[0].m_obj;
lean_object* v_x_69_ = stack[1].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_x_68_, v_x_69_);
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0___boxed(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_x_77_, v_x_78_);
lean_dec(v_x_78_);
lean_dec(v_x_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_optFn(lean_object* v_p_81_, lean_object* v_c_82_, lean_object* v_s_83_){
_start:
{
lean_object* v_pos_84_; lean_object* v_iniSz_85_; lean_object* v_s_86_; lean_object* v_pos_87_; lean_object* v_errorMsg_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_pos_84_ = lean_ctor_get(v_s_83_, 2);
lean_inc(v_pos_84_);
v_iniSz_85_ = l_Lean_Parser_ParserState_stackSize(v_s_83_);
v_s_86_ = lean_apply_2(v_p_81_, v_c_82_, v_s_83_);
v_pos_87_ = lean_ctor_get(v_s_86_, 2);
lean_inc(v_pos_87_);
v_errorMsg_88_ = lean_ctor_get(v_s_86_, 4);
lean_inc(v_errorMsg_88_);
v___x_89_ = lean_box(0);
v___x_90_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_88_, v___x_89_);
lean_dec(v_errorMsg_88_);
if (v___x_90_ == 0)
{
uint8_t v_decide_91_; 
v_decide_91_ = lean_nat_dec_eq(v_pos_87_, v_pos_84_);
lean_dec(v_pos_87_);
if (v_decide_91_ == 0)
{
lean_dec(v_iniSz_85_);
lean_dec(v_pos_84_);
return v_s_86_;
}
else
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Parser_ParserState_restore(v_s_86_, v_iniSz_85_, v_pos_84_);
lean_dec(v_iniSz_85_);
return v___x_92_;
}
}
else
{
lean_dec(v_pos_87_);
lean_dec(v_iniSz_85_);
lean_dec(v_pos_84_);
return v_s_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(lean_object* v_p_93_, lean_object* v_c_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_zero_97_; uint8_t v_isZero_98_; 
v_zero_97_ = lean_unsigned_to_nat(0u);
v_isZero_98_ = lean_nat_dec_eq(v_x_95_, v_zero_97_);
if (v_isZero_98_ == 1)
{
lean_dec(v_x_95_);
lean_dec_ref(v_c_94_);
lean_dec_ref(v_p_93_);
return v_x_96_;
}
else
{
lean_object* v_s_99_; lean_object* v_errorMsg_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
lean_inc_ref(v_p_93_);
lean_inc_ref(v_c_94_);
v_s_99_ = lean_apply_2(v_p_93_, v_c_94_, v_x_96_);
v_errorMsg_100_ = lean_ctor_get(v_s_99_, 4);
lean_inc(v_errorMsg_100_);
v___x_101_ = ((lean_object*)(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0));
v___x_102_ = lean_box(0);
v___x_103_ = l_instBEqOption_beq___redArg(v___x_101_, v_errorMsg_100_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec(v_x_95_);
lean_dec_ref(v_c_94_);
lean_dec_ref(v_p_93_);
return v_s_99_;
}
else
{
lean_object* v_one_104_; lean_object* v_n_105_; 
v_one_104_ = lean_unsigned_to_nat(1u);
v_n_105_ = lean_nat_sub(v_x_95_, v_one_104_);
lean_dec(v_x_95_);
v_x_95_ = v_n_105_;
v_x_96_ = v_s_99_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_repeatFn(lean_object* v_n_107_, lean_object* v_p_108_, lean_object* v_c_109_, lean_object* v_s_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(v_p_108_, v_c_109_, v_n_107_, v_s_110_);
return v___x_111_;
}
}
lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object* v_s_115_, uint32_t v_c_116_, lean_object* v_expected_117_, uint8_t v_pushMissing_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_119_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__0));
v___x_120_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_121_ = lean_string_push(v___x_120_, v_c_116_);
v___x_122_ = lean_string_append(v___x_119_, v___x_121_);
lean_dec_ref(v___x_121_);
v___x_123_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_115_, v___x_124_, v_expected_117_, v_pushMissing_118_);
return v___x_125_;
}
}
LEAN_EXPORT void l_Lake_Toml_mkUnexpectedCharError_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_115_ = stack[0].m_obj;
uint32_t v_c_116_ = stack[1].m_num;
lean_object* v_expected_117_ = stack[2].m_obj;
uint8_t v_pushMissing_118_ = stack[3].m_num;
lean_object* v_res_126_;
v_res_126_ = l_Lake_Toml_mkUnexpectedCharError(v_s_115_, v_c_116_, v_expected_117_, v_pushMissing_118_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_mkUnexpectedCharError___boxed(lean_object* v_s_127_, lean_object* v_c_128_, lean_object* v_expected_129_, lean_object* v_pushMissing_130_){
_start:
{
uint32_t v_c_boxed_131_; uint8_t v_pushMissing_boxed_132_; lean_object* v_res_133_; 
v_c_boxed_131_ = lean_unbox_uint32(v_c_128_);
lean_dec(v_c_128_);
v_pushMissing_boxed_132_ = lean_unbox(v_pushMissing_130_);
v_res_133_ = l_Lake_Toml_mkUnexpectedCharError(v_s_127_, v_c_boxed_131_, v_expected_129_, v_pushMissing_boxed_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn(lean_object* v_p_134_, lean_object* v_expected_135_, lean_object* v_c_136_, lean_object* v_s_137_){
_start:
{
lean_object* v_pos_138_; lean_object* v_toInputContext_139_; uint8_t v___x_140_; 
v_pos_138_ = lean_ctor_get(v_s_137_, 2);
v_toInputContext_139_ = lean_ctor_get(v_c_136_, 0);
v___x_140_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_139_, v_pos_138_);
if (v___x_140_ == 0)
{
lean_object* v_inputString_141_; uint32_t v_curr_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_inputString_141_ = lean_ctor_get(v_toInputContext_139_, 0);
v_curr_142_ = lean_string_utf8_get_fast(v_inputString_141_, v_pos_138_);
v___x_143_ = lean_box_uint32(v_curr_142_);
v___x_144_ = lean_apply_1(v_p_134_, v___x_143_);
v___x_145_ = lean_unbox(v___x_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; lean_object* v___x_147_; 
v___x_146_ = 1;
v___x_147_ = l_Lake_Toml_mkUnexpectedCharError(v_s_137_, v_curr_142_, v_expected_135_, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; 
lean_inc(v_pos_138_);
lean_dec(v_expected_135_);
v___x_148_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_137_, v_c_136_, v_pos_138_);
lean_dec(v_pos_138_);
return v___x_148_;
}
}
else
{
lean_object* v___x_149_; 
lean_dec_ref(v_p_134_);
v___x_149_ = l_Lean_Parser_ParserState_mkEOIError(v_s_137_, v_expected_135_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_satisfyFn___boxed(lean_object* v_p_150_, lean_object* v_expected_151_, lean_object* v_c_152_, lean_object* v_s_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lake_Toml_satisfyFn(v_p_150_, v_expected_151_, v_c_152_, v_s_153_);
lean_dec_ref(v_c_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn(lean_object* v_p_155_, lean_object* v_expected_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___y_160_; lean_object* v_pos_165_; lean_object* v_toInputContext_166_; uint8_t v___x_167_; 
v_pos_165_ = lean_ctor_get(v_a_158_, 2);
v_toInputContext_166_ = lean_ctor_get(v_a_157_, 0);
v___x_167_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_166_, v_pos_165_);
if (v___x_167_ == 0)
{
lean_object* v_inputString_168_; uint32_t v_curr_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_inputString_168_ = lean_ctor_get(v_toInputContext_166_, 0);
v_curr_169_ = lean_string_utf8_get_fast(v_inputString_168_, v_pos_165_);
v___x_170_ = lean_box_uint32(v_curr_169_);
lean_inc_ref(v_p_155_);
v___x_171_ = lean_apply_1(v_p_155_, v___x_170_);
v___x_172_ = lean_unbox(v___x_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; lean_object* v___x_174_; 
v___x_173_ = 1;
v___x_174_ = l_Lake_Toml_mkUnexpectedCharError(v_a_158_, v_curr_169_, v_expected_156_, v___x_173_);
v___y_160_ = v___x_174_;
goto v___jp_159_;
}
else
{
lean_object* v___x_175_; 
lean_inc(v_pos_165_);
lean_dec(v_expected_156_);
v___x_175_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_158_, v_a_157_, v_pos_165_);
lean_dec(v_pos_165_);
v___y_160_ = v___x_175_;
goto v___jp_159_;
}
}
else
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Parser_ParserState_mkEOIError(v_a_158_, v_expected_156_);
v___y_160_ = v___x_176_;
goto v___jp_159_;
}
v___jp_159_:
{
lean_object* v_errorMsg_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_errorMsg_161_ = lean_ctor_get(v___y_160_, 4);
v___x_162_ = lean_box(0);
v___x_163_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_dec_ref(v_p_155_);
return v___y_160_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Parser_takeWhileFn(v_p_155_, v_a_157_, v___y_160_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_takeWhile1Fn___boxed(lean_object* v_p_177_, lean_object* v_expected_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lake_Toml_takeWhile1Fn(v_p_177_, v_expected_178_, v_a_179_, v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn(lean_object* v_expected_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_pos_185_; lean_object* v_toInputContext_186_; uint8_t v___x_187_; 
v_pos_185_ = lean_ctor_get(v_a_184_, 2);
v_toInputContext_186_ = lean_ctor_get(v_a_183_, 0);
v___x_187_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_186_, v_pos_185_);
if (v___x_187_ == 0)
{
lean_object* v_inputString_188_; uint32_t v_curr_189_; uint32_t v___x_193_; uint8_t v___x_194_; 
v_inputString_188_ = lean_ctor_get(v_toInputContext_186_, 0);
v_curr_189_ = lean_string_utf8_get_fast(v_inputString_188_, v_pos_185_);
v___x_193_ = 48;
v___x_194_ = lean_uint32_dec_le(v___x_193_, v_curr_189_);
if (v___x_194_ == 0)
{
goto v___jp_190_;
}
else
{
uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_195_ = 57;
v___x_196_ = lean_uint32_dec_le(v_curr_189_, v___x_195_);
if (v___x_196_ == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v___x_197_; 
lean_inc(v_pos_185_);
lean_dec(v_expected_182_);
v___x_197_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_184_, v_a_183_, v_pos_185_);
lean_dec(v_pos_185_);
return v___x_197_;
}
}
v___jp_190_:
{
uint8_t v___x_191_; lean_object* v___x_192_; 
v___x_191_ = 1;
v___x_192_ = l_Lake_Toml_mkUnexpectedCharError(v_a_184_, v_curr_189_, v_expected_182_, v___x_191_);
return v___x_192_;
}
}
else
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Parser_ParserState_mkEOIError(v_a_184_, v_expected_182_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitFn___boxed(lean_object* v_expected_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lake_Toml_digitFn(v_expected_199_, v_a_200_, v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn(lean_object* v_expected_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_s_206_; lean_object* v_errorMsg_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
lean_inc(v_expected_203_);
v_s_206_ = l_Lake_Toml_digitFn(v_expected_203_, v_a_204_, v_a_205_);
v_errorMsg_207_ = lean_ctor_get(v_s_206_, 4);
v___x_208_ = lean_box(0);
v___x_209_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec(v_expected_203_);
return v_s_206_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = l_Lake_Toml_digitFn(v_expected_203_, v_a_204_, v_s_206_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_digitPairFn___boxed(lean_object* v_expected_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_Toml_digitPairFn(v_expected_211_, v_a_212_, v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_214_;
}
}
lean_object* l_Lake_Toml_chFn(uint32_t v_c_215_, lean_object* v_expected_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_pos_219_; lean_object* v_toInputContext_220_; uint8_t v___x_221_; 
v_pos_219_ = lean_ctor_get(v_a_218_, 2);
v_toInputContext_220_ = lean_ctor_get(v_a_217_, 0);
v___x_221_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_220_, v_pos_219_);
if (v___x_221_ == 0)
{
lean_object* v_inputString_222_; uint32_t v_curr_223_; uint8_t v___x_224_; 
v_inputString_222_ = lean_ctor_get(v_toInputContext_220_, 0);
v_curr_223_ = lean_string_utf8_get_fast(v_inputString_222_, v_pos_219_);
v___x_224_ = lean_uint32_dec_eq(v_curr_223_, v_c_215_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = 1;
v___x_226_ = l_Lake_Toml_mkUnexpectedCharError(v_a_218_, v_curr_223_, v_expected_216_, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; 
lean_inc(v_pos_219_);
lean_dec(v_expected_216_);
v___x_227_ = l_Lean_Parser_ParserState_next_x27___redArg(v_a_218_, v_a_217_, v_pos_219_);
lean_dec(v_pos_219_);
return v___x_227_;
}
}
else
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Parser_ParserState_mkEOIError(v_a_218_, v_expected_216_);
return v___x_228_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_chFn_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_215_ = stack[0].m_num;
lean_object* v_expected_216_ = stack[1].m_obj;
lean_object* v_a_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lake_Toml_chFn(v_c_215_, v_expected_216_, v_a_217_, v_a_218_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_chFn___boxed(lean_object* v_c_230_, lean_object* v_expected_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
uint32_t v_c_boxed_234_; lean_object* v_res_235_; 
v_c_boxed_234_ = lean_unbox_uint32(v_c_230_);
lean_dec(v_c_230_);
v_res_235_ = l_Lake_Toml_chFn(v_c_boxed_234_, v_expected_231_, v_a_232_, v_a_233_);
lean_dec_ref(v_a_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn(lean_object* v_str_236_, lean_object* v_expected_237_, lean_object* v_strPos_238_, lean_object* v_c_239_, lean_object* v_s_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_string_utf8_at_end(v_str_236_, v_strPos_238_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; lean_object* v_s_243_; lean_object* v_errorMsg_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_242_ = lean_string_utf8_get_fast(v_str_236_, v_strPos_238_);
lean_inc(v_expected_237_);
v_s_243_ = l_Lake_Toml_chFn(v___x_242_, v_expected_237_, v_c_239_, v_s_240_);
v_errorMsg_244_ = lean_ctor_get(v_s_243_, 4);
v___x_245_ = lean_box(0);
v___x_246_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v_strPos_238_);
lean_dec(v_expected_237_);
return v_s_243_;
}
else
{
if (v___x_241_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_string_utf8_next_fast(v_str_236_, v_strPos_238_);
lean_dec(v_strPos_238_);
v_strPos_238_ = v___x_247_;
v_s_240_ = v_s_243_;
goto _start;
}
else
{
lean_dec(v_strPos_238_);
lean_dec(v_expected_237_);
return v_s_243_;
}
}
}
else
{
lean_dec(v_strPos_238_);
lean_dec(v_expected_237_);
return v_s_240_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAuxFn___boxed(lean_object* v_str_249_, lean_object* v_expected_250_, lean_object* v_strPos_251_, lean_object* v_c_252_, lean_object* v_s_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lake_Toml_strAuxFn(v_str_249_, v_expected_250_, v_strPos_251_, v_c_252_, v_s_253_);
lean_dec_ref(v_c_252_);
lean_dec_ref(v_str_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strFn(lean_object* v_str_255_, lean_object* v_expected_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_alloc_closure((void*)(l_Lake_Toml_strAuxFn___boxed), 5, 3);
lean_closure_set(v___x_260_, 0, v_str_255_);
lean_closure_set(v___x_260_, 1, v_expected_256_);
lean_closure_set(v___x_260_, 2, v___x_259_);
v___x_261_ = l_Lean_Parser_atomicFn(v___x_260_, v_a_257_, v_a_258_);
return v___x_261_;
}
}
lean_object* l_Lake_Toml_sepByChar1Fn(lean_object* v_p_263_, uint32_t v_sep_264_, lean_object* v_expected_265_, lean_object* v_c_266_, lean_object* v_s_267_){
_start:
{
lean_object* v_pos_268_; lean_object* v_toInputContext_269_; uint8_t v___x_270_; 
v_pos_268_ = lean_ctor_get(v_s_267_, 2);
v_toInputContext_269_ = lean_ctor_get(v_c_266_, 0);
v___x_270_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_269_, v_pos_268_);
if (v___x_270_ == 0)
{
lean_object* v_inputString_271_; uint32_t v_curr_272_; lean_object* v_s_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
lean_inc(v_pos_268_);
v_inputString_271_ = lean_ctor_get(v_toInputContext_269_, 0);
v_curr_272_ = lean_string_utf8_get_fast(v_inputString_271_, v_pos_268_);
v_s_273_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_267_, v_c_266_, v_pos_268_);
lean_dec(v_pos_268_);
v___x_274_ = lean_box_uint32(v_curr_272_);
lean_inc_ref(v_p_263_);
v___x_275_ = lean_apply_1(v_p_263_, v___x_274_);
v___x_276_ = lean_unbox(v___x_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; uint8_t v___x_278_; 
lean_dec_ref(v_p_263_);
v___x_277_ = 1;
v___x_278_ = lean_uint32_dec_eq(v_curr_272_, v_sep_264_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = l_Lake_Toml_mkUnexpectedCharError(v_s_273_, v_curr_272_, v_expected_265_, v___x_277_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_280_ = ((lean_object*)(l_Lake_Toml_sepByChar1Fn___closed__0));
v___x_281_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_282_ = lean_string_push(v___x_281_, v_curr_272_);
v___x_283_ = lean_string_append(v___x_280_, v___x_282_);
lean_dec_ref(v___x_282_);
v___x_284_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__2));
v___x_285_ = lean_string_append(v___x_283_, v___x_284_);
v___x_286_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_273_, v___x_285_, v_expected_265_, v___x_277_);
return v___x_286_;
}
}
else
{
lean_object* v___x_287_; 
v___x_287_ = l_Lake_Toml_sepByChar1AuxFn(v_p_263_, v_sep_264_, v_expected_265_, v_c_266_, v_s_273_);
return v___x_287_;
}
}
else
{
lean_dec(v_expected_265_);
lean_dec_ref(v_p_263_);
return v_s_267_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_sepByChar1Fn_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_263_ = stack[0].m_obj;
uint32_t v_sep_264_ = stack[1].m_num;
lean_object* v_expected_265_ = stack[2].m_obj;
lean_object* v_c_266_ = stack[3].m_obj;
lean_object* v_s_267_ = stack[4].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lake_Toml_sepByChar1Fn(v_p_263_, v_sep_264_, v_expected_265_, v_c_266_, v_s_267_);
stack->m_obj
 = v_res_288_;
}
lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object* v_p_289_, uint32_t v_sep_290_, lean_object* v_expected_291_, lean_object* v_c_292_, lean_object* v_s_293_){
_start:
{
lean_object* v_pos_294_; lean_object* v_toInputContext_295_; uint8_t v___x_296_; 
v_pos_294_ = lean_ctor_get(v_s_293_, 2);
v_toInputContext_295_ = lean_ctor_get(v_c_292_, 0);
v___x_296_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_295_, v_pos_294_);
if (v___x_296_ == 0)
{
lean_object* v_inputString_297_; uint32_t v_curr_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_inputString_297_ = lean_ctor_get(v_toInputContext_295_, 0);
v_curr_298_ = lean_string_utf8_get_fast(v_inputString_297_, v_pos_294_);
v___x_299_ = lean_box_uint32(v_curr_298_);
lean_inc_ref(v_p_289_);
v___x_300_ = lean_apply_1(v_p_289_, v___x_299_);
v___x_301_ = lean_unbox(v___x_300_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
v___x_302_ = lean_uint32_dec_eq(v_curr_298_, v_sep_290_);
if (v___x_302_ == 0)
{
lean_dec(v_expected_291_);
lean_dec_ref(v_p_289_);
return v_s_293_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc(v_pos_294_);
v___x_303_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_293_, v_c_292_, v_pos_294_);
lean_dec(v_pos_294_);
v___x_304_ = l_Lake_Toml_sepByChar1Fn(v_p_289_, v_sep_290_, v_expected_291_, v_c_292_, v___x_303_);
return v___x_304_;
}
}
else
{
lean_object* v___x_305_; 
lean_inc(v_pos_294_);
v___x_305_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_293_, v_c_292_, v_pos_294_);
lean_dec(v_pos_294_);
v_s_293_ = v___x_305_;
goto _start;
}
}
else
{
lean_dec(v_expected_291_);
lean_dec_ref(v_p_289_);
return v_s_293_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_sepByChar1AuxFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_289_ = stack[0].m_obj;
uint32_t v_sep_290_ = stack[1].m_num;
lean_object* v_expected_291_ = stack[2].m_obj;
lean_object* v_c_292_ = stack[3].m_obj;
lean_object* v_s_293_ = stack[4].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_Lake_Toml_sepByChar1AuxFn(v_p_289_, v_sep_290_, v_expected_291_, v_c_292_, v_s_293_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1AuxFn___boxed(lean_object* v_p_308_, lean_object* v_sep_309_, lean_object* v_expected_310_, lean_object* v_c_311_, lean_object* v_s_312_){
_start:
{
uint32_t v_sep_boxed_313_; lean_object* v_res_314_; 
v_sep_boxed_313_ = lean_unbox_uint32(v_sep_309_);
lean_dec(v_sep_309_);
v_res_314_ = l_Lake_Toml_sepByChar1AuxFn(v_p_308_, v_sep_boxed_313_, v_expected_310_, v_c_311_, v_s_312_);
lean_dec_ref(v_c_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByChar1Fn___boxed(lean_object* v_p_315_, lean_object* v_sep_316_, lean_object* v_expected_317_, lean_object* v_c_318_, lean_object* v_s_319_){
_start:
{
uint32_t v_sep_boxed_320_; lean_object* v_res_321_; 
v_sep_boxed_320_ = lean_unbox_uint32(v_sep_316_);
lean_dec(v_sep_316_);
v_res_321_ = l_Lake_Toml_sepByChar1Fn(v_p_315_, v_sep_boxed_320_, v_expected_317_, v_c_318_, v_s_319_);
lean_dec_ref(v_c_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushAtom(lean_object* v_startPos_322_, lean_object* v_trailingFn_323_, lean_object* v_c_324_, lean_object* v_s_325_){
_start:
{
lean_object* v_toInputContext_326_; lean_object* v_pos_327_; lean_object* v_inputString_328_; lean_object* v_endPos_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_349_; 
v_toInputContext_326_ = lean_ctor_get(v_c_324_, 0);
lean_inc_ref(v_toInputContext_326_);
v_pos_327_ = lean_ctor_get(v_s_325_, 2);
lean_inc(v_pos_327_);
v_inputString_328_ = lean_ctor_get(v_toInputContext_326_, 0);
v_endPos_329_ = lean_ctor_get(v_toInputContext_326_, 3);
v_isSharedCheck_349_ = !lean_is_exclusive(v_toInputContext_326_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_350_ = lean_ctor_get(v_toInputContext_326_, 2);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_toInputContext_326_, 1);
lean_dec(v_unused_351_);
v___x_331_ = v_toInputContext_326_;
v_isShared_332_ = v_isSharedCheck_349_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_endPos_329_);
lean_inc(v_inputString_328_);
lean_dec(v_toInputContext_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_349_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_leading_333_; lean_object* v_s_334_; lean_object* v_pos_335_; lean_object* v_val_336_; lean_object* v___y_338_; uint8_t v___x_346_; 
lean_inc(v_startPos_322_);
v_leading_333_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_324_, v_startPos_322_);
v_s_334_ = lean_apply_2(v_trailingFn_323_, v_c_324_, v_s_325_);
v_pos_335_ = lean_ctor_get(v_s_334_, 2);
lean_inc(v_pos_335_);
v_val_336_ = lean_string_utf8_extract(v_inputString_328_, v_startPos_322_, v_pos_327_);
v___x_346_ = lean_nat_dec_le(v_pos_335_, v_endPos_329_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v_pos_335_);
v___x_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_347_, 0, v_inputString_328_);
lean_ctor_set(v___x_347_, 1, v_pos_327_);
lean_ctor_set(v___x_347_, 2, v_endPos_329_);
v___y_338_ = v___x_347_;
goto v___jp_337_;
}
else
{
lean_object* v___x_348_; 
lean_dec(v_endPos_329_);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v_inputString_328_);
lean_ctor_set(v___x_348_, 1, v_pos_327_);
lean_ctor_set(v___x_348_, 2, v_pos_335_);
v___y_338_ = v___x_348_;
goto v___jp_337_;
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = lean_string_utf8_byte_size(v_val_336_);
v___x_340_ = lean_nat_add(v_startPos_322_, v___x_339_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 3, v___x_340_);
lean_ctor_set(v___x_331_, 2, v___y_338_);
lean_ctor_set(v___x_331_, 1, v_startPos_322_);
lean_ctor_set(v___x_331_, 0, v_leading_333_);
v___x_342_ = v___x_331_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_leading_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_startPos_322_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v___y_338_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v___x_340_);
v___x_342_ = v_reuseFailAlloc_345_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v_atom_343_; lean_object* v___x_344_; 
v_atom_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_343_, 0, v___x_342_);
lean_ctor_set(v_atom_343_, 1, v_val_336_);
v___x_344_ = l_Lean_Parser_ParserState_pushSyntax(v_s_334_, v_atom_343_);
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atomFn(lean_object* v_p_352_, lean_object* v_trailingFn_353_, lean_object* v_c_354_, lean_object* v_s_355_){
_start:
{
lean_object* v_pos_356_; lean_object* v_s_357_; lean_object* v_errorMsg_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_pos_356_ = lean_ctor_get(v_s_355_, 2);
lean_inc(v_pos_356_);
lean_inc_ref(v_c_354_);
v_s_357_ = lean_apply_2(v_p_352_, v_c_354_, v_s_355_);
v_errorMsg_358_ = lean_ctor_get(v_s_357_, 4);
lean_inc(v_errorMsg_358_);
v___x_359_ = lean_box(0);
v___x_360_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_358_, v___x_359_);
lean_dec(v_errorMsg_358_);
if (v___x_360_ == 0)
{
lean_dec(v_pos_356_);
lean_dec_ref(v_c_354_);
lean_dec_ref(v_trailingFn_353_);
return v_s_357_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = l_Lake_Toml_pushAtom(v_pos_356_, v_trailingFn_353_, v_c_354_, v_s_357_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0(lean_object* v___y_362_){
_start:
{
lean_inc(v___y_362_);
return v___y_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__0___boxed(lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lake_Toml_atom___lam__0(v___y_363_);
lean_dec(v___y_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1(lean_object* v___y_365_){
_start:
{
lean_inc_ref(v___y_365_);
return v___y_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom___lam__1___boxed(lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lake_Toml_atom___lam__1(v___y_366_);
lean_dec_ref(v___y_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom(lean_object* v_p_374_, lean_object* v_trailingFn_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_377_ = lean_alloc_closure((void*)(l_Lake_Toml_atomFn), 4, 2);
lean_closure_set(v___x_377_, 0, v_p_374_);
lean_closure_set(v___x_377_, 1, v_trailingFn_375_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
return v___x_378_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_stxTrav_382_; lean_object* v_cur_383_; lean_object* v___x_384_; 
v___x_381_ = lean_st_ref_get(v___y_379_);
v_stxTrav_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_stxTrav_382_);
lean_dec(v___x_381_);
v_cur_383_ = lean_ctor_get(v_stxTrav_382_, 0);
lean_inc(v_cur_383_);
lean_dec_ref(v_stxTrav_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_cur_383_);
return v___x_384_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_379_ = stack[0].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_379_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_386_);
lean_dec(v___y_386_);
return v_res_388_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v___y_390_);
return v___x_394_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_389_ = stack[0].m_obj;
lean_object* v___y_390_ = stack[1].m_obj;
lean_object* v___y_391_ = stack[2].m_obj;
lean_object* v___y_392_ = stack[3].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(v___y_389_, v___y_390_, v___y_391_, v___y_392_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_401_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; lean_object* v_stxTrav_405_; lean_object* v_leadWord_406_; uint8_t v_leadWordIdent_407_; uint8_t v_isUngrouped_408_; uint8_t v_mustBeGrouped_409_; lean_object* v_stack_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v___x_404_ = lean_st_ref_take(v___y_402_);
v_stxTrav_405_ = lean_ctor_get(v___x_404_, 0);
v_leadWord_406_ = lean_ctor_get(v___x_404_, 1);
v_leadWordIdent_407_ = lean_ctor_get_uint8(v___x_404_, sizeof(void*)*3);
v_isUngrouped_408_ = lean_ctor_get_uint8(v___x_404_, sizeof(void*)*3 + 1);
v_mustBeGrouped_409_ = lean_ctor_get_uint8(v___x_404_, sizeof(void*)*3 + 2);
v_stack_410_ = lean_ctor_get(v___x_404_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_421_ == 0)
{
v___x_412_ = v___x_404_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_stack_410_);
lean_inc(v_leadWord_406_);
lean_inc(v_stxTrav_405_);
lean_dec(v___x_404_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_box(0);
v___x_415_ = l_Lean_Syntax_Traverser_left(v_stxTrav_405_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_leadWord_406_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_stack_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*3, v_leadWordIdent_407_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*3 + 1, v_isUngrouped_408_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*3 + 2, v_mustBeGrouped_409_);
v___x_417_ = v_reuseFailAlloc_420_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_st_ref_put(v___y_402_, v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_414_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_402_ = stack[0].m_obj;
lean_object* v_res_422_;
v_res_422_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_402_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_423_);
lean_dec(v___y_423_);
return v_res_425_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v___y_427_);
return v___x_431_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_426_ = stack[0].m_obj;
lean_object* v___y_427_ = stack[1].m_obj;
lean_object* v___y_428_ = stack[2].m_obj;
lean_object* v___y_429_ = stack[3].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(v___y_426_, v___y_427_, v___y_428_, v___y_429_);
stack->m_obj
 = v_res_432_;
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
v___x_439_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_442_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_443_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
lean_ctor_set(v___x_445_, 3, v___x_444_);
lean_ctor_set(v___x_445_, 4, v___x_443_);
lean_ctor_set(v___x_445_, 5, v___x_443_);
lean_ctor_set(v___x_445_, 6, v___x_443_);
lean_ctor_set(v___x_445_, 7, v___x_443_);
lean_ctor_set(v___x_445_, 8, v___x_443_);
lean_ctor_set(v___x_445_, 9, v___x_443_);
lean_ctor_set(v___x_445_, 10, v___x_443_);
lean_ctor_set(v___x_445_, 11, v___x_442_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(32u);
v___x_447_ = lean_mk_empty_array_with_capacity(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = ((size_t)5ULL);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_unsigned_to_nat(32u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3);
v___x_454_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
lean_ctor_set(v___x_454_, 2, v___x_450_);
lean_ctor_set(v___x_454_, 3, v___x_450_);
lean_ctor_set_usize(v___x_454_, 4, v___x_449_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_box(1);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_455_);
return v___x_458_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(lean_object* v_msgData_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; lean_object* v_toCold_464_; lean_object* v_env_465_; lean_object* v_options_466_; uint8_t v___x_467_; lean_object* v_env_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_463_ = lean_st_ref_get(v___y_461_);
v_toCold_464_ = lean_ctor_get(v___y_460_, 0);
v_env_465_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_463_);
v_options_466_ = lean_ctor_get(v_toCold_464_, 2);
v___x_467_ = 0;
v_env_468_ = l_Lean_Environment_setRecordingDeps(v_env_465_, v___x_467_);
v___x_469_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
v___x_470_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_466_);
v___x_471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_471_, 0, v_env_468_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
lean_ctor_set(v___x_471_, 3, v_options_466_);
v___x_472_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_msgData_459_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_459_ = stack[0].m_obj;
lean_object* v___y_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_459_, v___y_460_, v___y_461_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_479_;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_480_; double v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_float_of_nat(v___x_480_);
return v___x_481_;
}
}
lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* v_cls_484_, lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_ref_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_536_; 
v_ref_489_ = lean_ctor_get(v___y_486_, 2);
v___x_490_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_485_, v___y_486_, v___y_487_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_536_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_536_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_536_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v_traceState_496_; lean_object* v_env_497_; lean_object* v_nextMacroScope_498_; lean_object* v_ngen_499_; lean_object* v_auxDeclNGen_500_; lean_object* v_cache_501_; lean_object* v_recordedDeps_502_; lean_object* v_messages_503_; lean_object* v_infoState_504_; lean_object* v_snapshotTasks_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_535_; 
v___x_495_ = lean_st_ref_take(v___y_487_);
v_traceState_496_ = lean_ctor_get(v___x_495_, 4);
v_env_497_ = lean_ctor_get(v___x_495_, 0);
v_nextMacroScope_498_ = lean_ctor_get(v___x_495_, 1);
v_ngen_499_ = lean_ctor_get(v___x_495_, 2);
v_auxDeclNGen_500_ = lean_ctor_get(v___x_495_, 3);
v_cache_501_ = lean_ctor_get(v___x_495_, 5);
v_recordedDeps_502_ = lean_ctor_get(v___x_495_, 6);
v_messages_503_ = lean_ctor_get(v___x_495_, 7);
v_infoState_504_ = lean_ctor_get(v___x_495_, 8);
v_snapshotTasks_505_ = lean_ctor_get(v___x_495_, 9);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_535_ == 0)
{
v___x_507_ = v___x_495_;
v_isShared_508_ = v_isSharedCheck_535_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snapshotTasks_505_);
lean_inc(v_infoState_504_);
lean_inc(v_messages_503_);
lean_inc(v_recordedDeps_502_);
lean_inc(v_cache_501_);
lean_inc(v_traceState_496_);
lean_inc(v_auxDeclNGen_500_);
lean_inc(v_ngen_499_);
lean_inc(v_nextMacroScope_498_);
lean_inc(v_env_497_);
lean_dec(v___x_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_535_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint64_t v_tid_509_; lean_object* v_traces_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_534_; 
v_tid_509_ = lean_ctor_get_uint64(v_traceState_496_, sizeof(void*)*1);
v_traces_510_ = lean_ctor_get(v_traceState_496_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_traceState_496_);
if (v_isSharedCheck_534_ == 0)
{
v___x_512_ = v_traceState_496_;
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_traces_510_);
lean_dec(v_traceState_496_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; double v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_514_ = lean_box(0);
v___x_515_ = lean_box(0);
v___x_516_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_517_ = 0;
v___x_518_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_519_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_519_, 0, v_cls_484_);
lean_ctor_set(v___x_519_, 1, v___x_515_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
lean_ctor_set_float(v___x_519_, sizeof(void*)*3, v___x_516_);
lean_ctor_set_float(v___x_519_, sizeof(void*)*3 + 8, v___x_516_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*3 + 16, v___x_517_);
v___x_520_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_521_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v_a_491_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
lean_inc(v_ref_489_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_ref_489_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_PersistentArray_push___redArg(v_traces_510_, v___x_522_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_523_);
v___x_525_ = v___x_512_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_523_);
lean_ctor_set_uint64(v_reuseFailAlloc_533_, sizeof(void*)*1, v_tid_509_);
v___x_525_ = v_reuseFailAlloc_533_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 4, v___x_525_);
v___x_527_ = v___x_507_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_env_497_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_nextMacroScope_498_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_ngen_499_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_auxDeclNGen_500_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_532_, 5, v_cache_501_);
lean_ctor_set(v_reuseFailAlloc_532_, 6, v_recordedDeps_502_);
lean_ctor_set(v_reuseFailAlloc_532_, 7, v_messages_503_);
lean_ctor_set(v_reuseFailAlloc_532_, 8, v_infoState_504_);
lean_ctor_set(v_reuseFailAlloc_532_, 9, v_snapshotTasks_505_);
v___x_527_ = v_reuseFailAlloc_532_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_st_ref_put(v___y_487_, v___x_527_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_514_);
v___x_530_ = v___x_493_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_514_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_484_ = stack[0].m_obj;
lean_object* v_msg_485_ = stack[1].m_obj;
lean_object* v___y_486_ = stack[2].m_obj;
lean_object* v___y_487_ = stack[3].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_484_, v_msg_485_, v___y_486_, v___y_487_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_538_, v_msg_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_543_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_555_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__5));
v___x_556_ = l_Lean_Name_append(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__8(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__7));
v___x_559_ = l_Lean_stringToMessageData(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__10(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__9));
v___x_562_ = l_Lean_stringToMessageData(v___x_561_);
return v___x_562_;
}
}
lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; lean_object* v_a_569_; 
v___x_568_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_564_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
if (lean_obj_tag(v_a_569_) == 2)
{
lean_object* v_info_570_; lean_object* v_val_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_info_570_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_info_570_);
v_val_571_ = lean_ctor_get(v_a_569_, 1);
lean_inc_ref(v_val_571_);
v___x_572_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_569_);
lean_dec_ref_known(v_a_569_, 2);
v___x_573_ = 0;
v___x_574_ = lean_box(v___x_573_);
v___x_575_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_575_, 0, v_info_570_);
lean_closure_set(v___x_575_, 1, v_val_571_);
lean_closure_set(v___x_575_, 2, v___x_574_);
v___x_576_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_572_, v___x_575_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
lean_dec(v___x_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; 
lean_dec_ref_known(v___x_576_, 1);
v___x_577_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_564_);
return v___x_577_;
}
else
{
return v___x_576_;
}
}
else
{
lean_object* v_toCold_578_; lean_object* v_options_579_; uint8_t v_hasTrace_580_; 
v_toCold_578_ = lean_ctor_get(v_a_565_, 0);
v_options_579_ = lean_ctor_get(v_toCold_578_, 2);
v_hasTrace_580_ = lean_ctor_get_uint8(v_options_579_, sizeof(void*)*1);
if (v_hasTrace_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec(v_a_569_);
v___x_581_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_581_;
}
else
{
lean_object* v_inheritedTraceOptions_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_inheritedTraceOptions_582_ = lean_ctor_get(v_toCold_578_, 11);
v___x_583_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_584_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_585_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_582_, v_options_579_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v_a_569_);
v___x_586_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_587_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_588_ = lean_box(0);
v___x_589_ = 0;
v___x_590_ = l_Lean_Syntax_formatStx(v_a_569_, v___x_588_, v___x_589_);
v___x_591_ = l_Lean_MessageData_ofFormat(v___x_590_);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_587_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_583_, v___x_594_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_596_; 
lean_dec_ref_known(v___x_595_, 1);
v___x_596_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_596_;
}
else
{
return v___x_595_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_atom_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_563_ = stack[0].m_obj;
lean_object* v_a_564_ = stack[1].m_obj;
lean_object* v_a_565_ = stack[2].m_obj;
lean_object* v_a_566_ = stack[3].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_Lake_Toml_atom_formatter___redArg(v_a_563_, v_a_564_, v_a_565_, v_a_566_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lake_Toml_atom_formatter___redArg(v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_603_;
}
}
lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lake_Toml_atom_formatter___redArg(v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_611_;
}
}
LEAN_EXPORT void l_Lake_Toml_atom_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_604_ = stack[0].m_obj;
lean_object* v_x_605_ = stack[1].m_obj;
lean_object* v_a_606_ = stack[2].m_obj;
lean_object* v_a_607_ = stack[3].m_obj;
lean_object* v_a_608_ = stack[4].m_obj;
lean_object* v_a_609_ = stack[5].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_Lake_Toml_atom_formatter(v_x_604_, v_x_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lake_Toml_atom_formatter(v_x_613_, v_x_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec_ref(v_x_614_);
lean_dec_ref(v_x_613_);
return v_res_620_;
}
}
lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_621_, lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_621_, v_msg_622_, v___y_625_, v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_621_ = stack[0].m_obj;
lean_object* v_msg_622_ = stack[1].m_obj;
lean_object* v___y_623_ = stack[2].m_obj;
lean_object* v___y_624_ = stack[3].m_obj;
lean_object* v___y_625_ = stack[4].m_obj;
lean_object* v___y_626_ = stack[5].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_621_, v_msg_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_630_, lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_630_, v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_638_);
return v___x_640_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_638_ = stack[0].m_obj;
lean_object* v_res_641_;
v_res_641_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_638_);
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_642_);
lean_dec(v_a_642_);
return v_res_644_;
}
}
lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_648_);
return v___x_652_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_645_ = stack[0].m_obj;
lean_object* v_x_646_ = stack[1].m_obj;
lean_object* v_a_647_ = stack[2].m_obj;
lean_object* v_a_648_ = stack[3].m_obj;
lean_object* v_a_649_ = stack[4].m_obj;
lean_object* v_a_650_ = stack[5].m_obj;
lean_object* v_res_653_;
v_res_653_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_645_, v_x_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
stack->m_obj
 = v_res_653_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_654_, v_x_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec_ref(v_x_655_);
lean_dec_ref(v_x_654_);
return v_res_661_;
}
}
lean_object* l_Lake_Toml_chAtom(uint32_t v_c_662_, lean_object* v_expected_663_, lean_object* v_trailingFn_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_box_uint32(v_c_662_);
v___x_666_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_666_, 0, v___x_665_);
lean_closure_set(v___x_666_, 1, v_expected_663_);
v___x_667_ = l_Lake_Toml_atom(v___x_666_, v_trailingFn_664_);
return v___x_667_;
}
}
LEAN_EXPORT void l_Lake_Toml_chAtom_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_662_ = stack[0].m_num;
lean_object* v_expected_663_ = stack[1].m_obj;
lean_object* v_trailingFn_664_ = stack[2].m_obj;
lean_object* v_res_668_;
v_res_668_ = l_Lake_Toml_chAtom(v_c_662_, v_expected_663_, v_trailingFn_664_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_669_, lean_object* v_expected_670_, lean_object* v_trailingFn_671_){
_start:
{
uint32_t v_c_boxed_672_; lean_object* v_res_673_; 
v_c_boxed_672_ = lean_unbox_uint32(v_c_669_);
lean_dec(v_c_669_);
v_res_673_ = l_Lake_Toml_chAtom(v_c_boxed_672_, v_expected_670_, v_trailingFn_671_);
return v_res_673_;
}
}
lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
uint8_t v___x_680_; lean_object* v___x_681_; 
v___x_680_ = 0;
v___x_681_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_674_, v___x_680_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v___x_681_;
}
}
LEAN_EXPORT void l_Lake_Toml_chAtom_formatter___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_674_ = stack[0].m_num;
lean_object* v_a_675_ = stack[1].m_obj;
lean_object* v_a_676_ = stack[2].m_obj;
lean_object* v_a_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
uint32_t v_c_boxed_689_; lean_object* v_res_690_; 
v_c_boxed_689_ = lean_unbox_uint32(v_c_683_);
lean_dec(v_c_683_);
v_res_690_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_689_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_690_;
}
}
lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_691_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_699_;
}
}
LEAN_EXPORT void l_Lake_Toml_chAtom_formatter_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_691_ = stack[0].m_num;
lean_object* v_x_692_ = stack[1].m_obj;
lean_object* v_x_693_ = stack[2].m_obj;
lean_object* v_a_694_ = stack[3].m_obj;
lean_object* v_a_695_ = stack[4].m_obj;
lean_object* v_a_696_ = stack[5].m_obj;
lean_object* v_a_697_ = stack[6].m_obj;
lean_object* v_res_700_;
v_res_700_ = l_Lake_Toml_chAtom_formatter(v_c_691_, v_x_692_, v_x_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
stack->m_obj
 = v_res_700_;
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
lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_711_);
return v___x_713_;
}
}
LEAN_EXPORT void l_Lake_Toml_chAtom_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_711_ = stack[0].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_711_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_715_);
lean_dec(v_a_715_);
return v_res_717_;
}
}
lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_722_);
return v___x_726_;
}
}
LEAN_EXPORT void l_Lake_Toml_chAtom_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_718_ = stack[0].m_num;
lean_object* v_x_719_ = stack[1].m_obj;
lean_object* v_x_720_ = stack[2].m_obj;
lean_object* v_a_721_ = stack[3].m_obj;
lean_object* v_a_722_ = stack[4].m_obj;
lean_object* v_a_723_ = stack[5].m_obj;
lean_object* v_a_724_ = stack[6].m_obj;
lean_object* v_res_727_;
v_res_727_ = l_Lake_Toml_chAtom_parenthesizer(v_x_718_, v_x_719_, v_x_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
uint32_t v_x_22__boxed_736_; lean_object* v_res_737_; 
v_x_22__boxed_736_ = lean_unbox_uint32(v_x_728_);
lean_dec(v_x_728_);
v_res_737_ = l_Lake_Toml_chAtom_parenthesizer(v_x_22__boxed_736_, v_x_729_, v_x_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec_ref(v_x_730_);
lean_dec(v_x_729_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_738_, lean_object* v_expected_739_, lean_object* v_trailingFn_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_str_745_; lean_object* v_startInclusive_746_; lean_object* v_endExclusive_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_string_utf8_byte_size(v_s_738_);
v___x_743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_743_, 0, v_s_738_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
v___x_744_ = l_String_Slice_trimAscii(v___x_743_);
v_str_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_str_745_);
v_startInclusive_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_startInclusive_746_);
v_endExclusive_747_ = lean_ctor_get(v___x_744_, 2);
lean_inc(v_endExclusive_747_);
lean_dec_ref(v___x_744_);
v___x_748_ = lean_string_utf8_extract_fast(v_str_745_, v_startInclusive_746_, v_endExclusive_747_);
lean_dec(v_endExclusive_747_);
lean_dec(v_startInclusive_746_);
lean_dec_ref(v_str_745_);
v___x_749_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_749_, 0, v___x_748_);
lean_closure_set(v___x_749_, 1, v_expected_739_);
v___x_750_ = l_Lake_Toml_atom(v___x_749_, v_trailingFn_740_);
return v___x_750_;
}
}
lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
return v___x_757_;
}
}
LEAN_EXPORT void l_Lake_Toml_strAtom_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_751_ = stack[0].m_obj;
lean_object* v_a_752_ = stack[1].m_obj;
lean_object* v_a_753_ = stack[2].m_obj;
lean_object* v_a_754_ = stack[3].m_obj;
lean_object* v_a_755_ = stack[4].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_765_;
}
}
lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_766_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
return v___x_774_;
}
}
LEAN_EXPORT void l_Lake_Toml_strAtom_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_766_ = stack[0].m_obj;
lean_object* v_x_767_ = stack[1].m_obj;
lean_object* v_x_768_ = stack[2].m_obj;
lean_object* v_a_769_ = stack[3].m_obj;
lean_object* v_a_770_ = stack[4].m_obj;
lean_object* v_a_771_ = stack[5].m_obj;
lean_object* v_a_772_ = stack[6].m_obj;
lean_object* v_res_775_;
v_res_775_ = l_Lake_Toml_strAtom_formatter(v_s_766_, v_x_767_, v_x_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lake_Toml_strAtom_formatter(v_s_776_, v_x_777_, v_x_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec_ref(v_x_778_);
lean_dec(v_x_777_);
return v_res_784_;
}
}
lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_785_);
return v___x_787_;
}
}
LEAN_EXPORT void l_Lake_Toml_strAtom_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_785_ = stack[0].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_785_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_789_);
lean_dec(v_a_789_);
return v_res_791_;
}
}
lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_796_);
return v___x_800_;
}
}
LEAN_EXPORT void l_Lake_Toml_strAtom_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_792_ = stack[0].m_obj;
lean_object* v_x_793_ = stack[1].m_obj;
lean_object* v_x_794_ = stack[2].m_obj;
lean_object* v_a_795_ = stack[3].m_obj;
lean_object* v_a_796_ = stack[4].m_obj;
lean_object* v_a_797_ = stack[5].m_obj;
lean_object* v_a_798_ = stack[6].m_obj;
lean_object* v_res_801_;
v_res_801_ = l_Lake_Toml_strAtom_parenthesizer(v_x_792_, v_x_793_, v_x_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
stack->m_obj
 = v_res_801_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lake_Toml_strAtom_parenthesizer(v_x_802_, v_x_803_, v_x_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec_ref(v_x_804_);
lean_dec(v_x_803_);
lean_dec_ref(v_x_802_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_811_, lean_object* v_startPos_812_, lean_object* v_trailingFn_813_, lean_object* v_c_814_, lean_object* v_s_815_){
_start:
{
lean_object* v_toInputContext_816_; lean_object* v_pos_817_; lean_object* v_inputString_818_; lean_object* v_endPos_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_837_; 
v_toInputContext_816_ = lean_ctor_get(v_c_814_, 0);
lean_inc_ref(v_toInputContext_816_);
v_pos_817_ = lean_ctor_get(v_s_815_, 2);
lean_inc(v_pos_817_);
v_inputString_818_ = lean_ctor_get(v_toInputContext_816_, 0);
v_endPos_819_ = lean_ctor_get(v_toInputContext_816_, 3);
v_isSharedCheck_837_ = !lean_is_exclusive(v_toInputContext_816_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; 
v_unused_838_ = lean_ctor_get(v_toInputContext_816_, 2);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_toInputContext_816_, 1);
lean_dec(v_unused_839_);
v___x_821_ = v_toInputContext_816_;
v_isShared_822_ = v_isSharedCheck_837_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_endPos_819_);
lean_inc(v_inputString_818_);
lean_dec(v_toInputContext_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_837_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_leading_823_; lean_object* v_s_824_; lean_object* v_pos_825_; lean_object* v_val_826_; lean_object* v___y_828_; uint8_t v___x_834_; 
lean_inc(v_startPos_812_);
v_leading_823_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_814_, v_startPos_812_);
v_s_824_ = lean_apply_2(v_trailingFn_813_, v_c_814_, v_s_815_);
v_pos_825_ = lean_ctor_get(v_s_824_, 2);
lean_inc(v_pos_825_);
v_val_826_ = lean_string_utf8_extract(v_inputString_818_, v_startPos_812_, v_pos_817_);
v___x_834_ = lean_nat_dec_le(v_pos_825_, v_endPos_819_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v_pos_825_);
lean_inc(v_pos_817_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v_inputString_818_);
lean_ctor_set(v___x_835_, 1, v_pos_817_);
lean_ctor_set(v___x_835_, 2, v_endPos_819_);
v___y_828_ = v___x_835_;
goto v___jp_827_;
}
else
{
lean_object* v___x_836_; 
lean_dec(v_endPos_819_);
lean_inc(v_pos_817_);
v___x_836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_836_, 0, v_inputString_818_);
lean_ctor_set(v___x_836_, 1, v_pos_817_);
lean_ctor_set(v___x_836_, 2, v_pos_825_);
v___y_828_ = v___x_836_;
goto v___jp_827_;
}
v___jp_827_:
{
lean_object* v_info_830_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 3, v_pos_817_);
lean_ctor_set(v___x_821_, 2, v___y_828_);
lean_ctor_set(v___x_821_, 1, v_startPos_812_);
lean_ctor_set(v___x_821_, 0, v_leading_823_);
v_info_830_ = v___x_821_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_leading_823_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_startPos_812_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v___y_828_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_pos_817_);
v_info_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = l_Lean_Syntax_mkLit(v_kind_811_, v_val_826_, v_info_830_);
v___x_832_ = l_Lean_Parser_ParserState_pushSyntax(v_s_824_, v___x_831_);
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_840_, lean_object* v_p_841_, lean_object* v_trailingFn_842_, lean_object* v_c_843_, lean_object* v_s_844_){
_start:
{
lean_object* v_pos_845_; lean_object* v_s_846_; lean_object* v_errorMsg_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_pos_845_ = lean_ctor_get(v_s_844_, 2);
lean_inc(v_pos_845_);
lean_inc_ref(v_c_843_);
v_s_846_ = lean_apply_2(v_p_841_, v_c_843_, v_s_844_);
v_errorMsg_847_ = lean_ctor_get(v_s_846_, 4);
lean_inc(v_errorMsg_847_);
v___x_848_ = lean_box(0);
v___x_849_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_847_, v___x_848_);
lean_dec(v_errorMsg_847_);
if (v___x_849_ == 0)
{
lean_dec(v_pos_845_);
lean_dec_ref(v_c_843_);
lean_dec_ref(v_trailingFn_842_);
lean_dec(v_kind_840_);
return v_s_846_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = l_Lake_Toml_pushLit(v_kind_840_, v_pos_845_, v_trailingFn_842_, v_c_843_, v_s_846_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_851_, lean_object* v_p_852_, lean_object* v_trailingFn_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_855_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_855_, 0, v_kind_851_);
lean_closure_set(v___x_855_, 1, v_p_852_);
lean_closure_set(v___x_855_, 2, v_trailingFn_853_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
return v___x_856_;
}
}
lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_863_;
}
}
LEAN_EXPORT void l_Lake_Toml_lit_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_857_ = stack[0].m_obj;
lean_object* v_a_858_ = stack[1].m_obj;
lean_object* v_a_859_ = stack[2].m_obj;
lean_object* v_a_860_ = stack[3].m_obj;
lean_object* v_a_861_ = stack[4].m_obj;
lean_object* v_res_864_;
v_res_864_ = l_Lake_Toml_lit_formatter___redArg(v_kind_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lake_Toml_lit_formatter___redArg(v_kind_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_871_;
}
}
lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_872_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_880_;
}
}
LEAN_EXPORT void l_Lake_Toml_lit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_872_ = stack[0].m_obj;
lean_object* v_x_873_ = stack[1].m_obj;
lean_object* v_x_874_ = stack[2].m_obj;
lean_object* v_a_875_ = stack[3].m_obj;
lean_object* v_a_876_ = stack[4].m_obj;
lean_object* v_a_877_ = stack[5].m_obj;
lean_object* v_a_878_ = stack[6].m_obj;
lean_object* v_res_881_;
v_res_881_ = l_Lake_Toml_lit_formatter(v_kind_872_, v_x_873_, v_x_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
stack->m_obj
 = v_res_881_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lake_Toml_lit_formatter(v_kind_882_, v_x_883_, v_x_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_x_884_);
lean_dec_ref(v_x_883_);
return v_res_890_;
}
}
lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_891_);
return v___x_893_;
}
}
LEAN_EXPORT void l_Lake_Toml_lit_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_891_ = stack[0].m_obj;
lean_object* v_res_894_;
v_res_894_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_891_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_895_);
lean_dec(v_a_895_);
return v_res_897_;
}
}
lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_902_);
return v___x_906_;
}
}
LEAN_EXPORT void l_Lake_Toml_lit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_898_ = stack[0].m_obj;
lean_object* v_x_899_ = stack[1].m_obj;
lean_object* v_x_900_ = stack[2].m_obj;
lean_object* v_a_901_ = stack[3].m_obj;
lean_object* v_a_902_ = stack[4].m_obj;
lean_object* v_a_903_ = stack[5].m_obj;
lean_object* v_a_904_ = stack[6].m_obj;
lean_object* v_res_907_;
v_res_907_ = l_Lake_Toml_lit_parenthesizer(v_x_898_, v_x_899_, v_x_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
stack->m_obj
 = v_res_907_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lake_Toml_lit_parenthesizer(v_x_908_, v_x_909_, v_x_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec_ref(v_x_910_);
lean_dec_ref(v_x_909_);
lean_dec(v_x_908_);
return v_res_916_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_917_ = stack[0].m_obj;
lean_object* v___y_918_ = stack[1].m_obj;
lean_object* v___y_919_ = stack[2].m_obj;
lean_object* v___y_920_ = stack[3].m_obj;
lean_object* v___y_921_ = stack[4].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_932_, lean_object* v_kind_933_, uint8_t v_anonymous_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___f_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_inc(v_kind_933_);
v___f_940_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_940_, 0, v_kind_933_);
v___x_941_ = 0;
v___x_942_ = lean_box(v_anonymous_934_);
v___x_943_ = lean_box(v___x_941_);
v___x_944_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_944_, 0, v_name_932_);
lean_closure_set(v___x_944_, 1, v_kind_933_);
lean_closure_set(v___x_944_, 2, v___x_942_);
lean_closure_set(v___x_944_, 3, v___x_943_);
v___x_945_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_944_, v___f_940_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_945_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_932_ = stack[0].m_obj;
lean_object* v_kind_933_ = stack[1].m_obj;
uint8_t v_anonymous_934_ = stack[2].m_num;
lean_object* v_a_935_ = stack[3].m_obj;
lean_object* v_a_936_ = stack[4].m_obj;
lean_object* v_a_937_ = stack[5].m_obj;
lean_object* v_a_938_ = stack[6].m_obj;
lean_object* v_res_946_;
v_res_946_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_932_, v_kind_933_, v_anonymous_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_947_, lean_object* v_kind_948_, lean_object* v_anonymous_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
uint8_t v_anonymous_boxed_955_; lean_object* v_res_956_; 
v_anonymous_boxed_955_ = lean_unbox(v_anonymous_949_);
v_res_956_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_947_, v_kind_948_, v_anonymous_boxed_955_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_956_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_957_, lean_object* v_kind_958_, lean_object* v_p_959_, lean_object* v_trailingFn_960_, uint8_t v_anonymous_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_957_, v_kind_958_, v_anonymous_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_957_ = stack[0].m_obj;
lean_object* v_kind_958_ = stack[1].m_obj;
lean_object* v_p_959_ = stack[2].m_obj;
lean_object* v_trailingFn_960_ = stack[3].m_obj;
uint8_t v_anonymous_961_ = stack[4].m_num;
lean_object* v_a_962_ = stack[5].m_obj;
lean_object* v_a_963_ = stack[6].m_obj;
lean_object* v_a_964_ = stack[7].m_obj;
lean_object* v_a_965_ = stack[8].m_obj;
lean_object* v_res_968_;
v_res_968_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_957_, v_kind_958_, v_p_959_, v_trailingFn_960_, v_anonymous_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_969_, lean_object* v_kind_970_, lean_object* v_p_971_, lean_object* v_trailingFn_972_, lean_object* v_anonymous_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_anonymous_boxed_979_; lean_object* v_res_980_; 
v_anonymous_boxed_979_ = lean_unbox(v_anonymous_973_);
v_res_980_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_969_, v_kind_970_, v_p_971_, v_trailingFn_972_, v_anonymous_boxed_979_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_trailingFn_972_);
lean_dec_ref(v_p_971_);
return v_res_980_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_982_);
return v___x_986_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_981_ = stack[0].m_obj;
lean_object* v___y_982_ = stack[1].m_obj;
lean_object* v___y_983_ = stack[2].m_obj;
lean_object* v___y_984_ = stack[3].m_obj;
lean_object* v_res_987_;
v_res_987_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_981_, v___y_982_, v___y_983_, v___y_984_);
stack->m_obj
 = v_res_987_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_993_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_995_, lean_object* v_kind_996_, uint8_t v_anonymous_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___f_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___f_1003_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_1004_ = 0;
v___x_1005_ = lean_box(v_anonymous_997_);
v___x_1006_ = lean_box(v___x_1004_);
v___x_1007_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1007_, 0, v_name_995_);
lean_closure_set(v___x_1007_, 1, v_kind_996_);
lean_closure_set(v___x_1007_, 2, v___x_1005_);
lean_closure_set(v___x_1007_, 3, v___x_1006_);
v___x_1008_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1007_, v___f_1003_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
return v___x_1008_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_995_ = stack[0].m_obj;
lean_object* v_kind_996_ = stack[1].m_obj;
uint8_t v_anonymous_997_ = stack[2].m_num;
lean_object* v_a_998_ = stack[3].m_obj;
lean_object* v_a_999_ = stack[4].m_obj;
lean_object* v_a_1000_ = stack[5].m_obj;
lean_object* v_a_1001_ = stack[6].m_obj;
lean_object* v_res_1009_;
v_res_1009_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_995_, v_kind_996_, v_anonymous_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
stack->m_obj
 = v_res_1009_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_1010_, lean_object* v_kind_1011_, lean_object* v_anonymous_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
uint8_t v_anonymous_boxed_1018_; lean_object* v_res_1019_; 
v_anonymous_boxed_1018_ = lean_unbox(v_anonymous_1012_);
v_res_1019_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_1010_, v_kind_1011_, v_anonymous_boxed_1018_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1019_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_1020_, lean_object* v_kind_1021_, lean_object* v_p_1022_, lean_object* v_trailingFn_1023_, uint8_t v_anonymous_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_1020_, v_kind_1021_, v_anonymous_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1020_ = stack[0].m_obj;
lean_object* v_kind_1021_ = stack[1].m_obj;
lean_object* v_p_1022_ = stack[2].m_obj;
lean_object* v_trailingFn_1023_ = stack[3].m_obj;
uint8_t v_anonymous_1024_ = stack[4].m_num;
lean_object* v_a_1025_ = stack[5].m_obj;
lean_object* v_a_1026_ = stack[6].m_obj;
lean_object* v_a_1027_ = stack[7].m_obj;
lean_object* v_a_1028_ = stack[8].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_1020_, v_kind_1021_, v_p_1022_, v_trailingFn_1023_, v_anonymous_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_1032_, lean_object* v_kind_1033_, lean_object* v_p_1034_, lean_object* v_trailingFn_1035_, lean_object* v_anonymous_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
uint8_t v_anonymous_boxed_1042_; lean_object* v_res_1043_; 
v_anonymous_boxed_1042_ = lean_unbox(v_anonymous_1036_);
v_res_1043_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_1032_, v_kind_1033_, v_p_1034_, v_trailingFn_1035_, v_anonymous_boxed_1042_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec_ref(v_trailingFn_1035_);
lean_dec_ref(v_p_1034_);
return v_res_1043_;
}
}
lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1044_, lean_object* v_kind_1045_, lean_object* v_p_1046_, lean_object* v_trailingFn_1047_, uint8_t v_anonymous_1048_){
_start:
{
uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = 0;
lean_inc(v_kind_1045_);
v___x_1050_ = l_Lean_Parser_mkAntiquot(v_name_1044_, v_kind_1045_, v_anonymous_1048_, v___x_1049_);
v___x_1051_ = l_Lake_Toml_lit(v_kind_1045_, v_p_1046_, v_trailingFn_1047_);
v___x_1052_ = l_Lean_Parser_withAntiquot(v___x_1050_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT void l_Lake_Toml_litWithAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1044_ = stack[0].m_obj;
lean_object* v_kind_1045_ = stack[1].m_obj;
lean_object* v_p_1046_ = stack[2].m_obj;
lean_object* v_trailingFn_1047_ = stack[3].m_obj;
uint8_t v_anonymous_1048_ = stack[4].m_num;
lean_object* v_res_1053_;
v_res_1053_ = l_Lake_Toml_litWithAntiquot(v_name_1044_, v_kind_1045_, v_p_1046_, v_trailingFn_1047_, v_anonymous_1048_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1054_, lean_object* v_kind_1055_, lean_object* v_p_1056_, lean_object* v_trailingFn_1057_, lean_object* v_anonymous_1058_){
_start:
{
uint8_t v_anonymous_boxed_1059_; lean_object* v_res_1060_; 
v_anonymous_boxed_1059_ = lean_unbox(v_anonymous_1058_);
v_res_1060_ = l_Lake_Toml_litWithAntiquot(v_name_1054_, v_kind_1055_, v_p_1056_, v_trailingFn_1057_, v_anonymous_boxed_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = l_Lean_Parser_epsilonInfo;
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_fn_1061_);
return v___x_1063_;
}
}
lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT void l_Lake_Toml_epsilon_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1067_;
v_res_1067_ = l_Lake_Toml_epsilon_formatter___redArg();
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1069_;
}
}
lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1076_;
}
}
LEAN_EXPORT void l_Lake_Toml_epsilon_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1070_ = stack[0].m_obj;
lean_object* v_a_1071_ = stack[1].m_obj;
lean_object* v_a_1072_ = stack[2].m_obj;
lean_object* v_a_1073_ = stack[3].m_obj;
lean_object* v_a_1074_ = stack[4].m_obj;
lean_object* v_res_1077_;
v_res_1077_ = l_Lake_Toml_epsilon_formatter(v_x_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
stack->m_obj
 = v_res_1077_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lake_Toml_epsilon_formatter(v_x_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec_ref(v_x_1078_);
return v_res_1084_;
}
}
lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT void l_Lake_Toml_epsilon_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1088_;
v_res_1088_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1090_;
}
}
lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1097_;
}
}
LEAN_EXPORT void l_Lake_Toml_epsilon_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1091_ = stack[0].m_obj;
lean_object* v_a_1092_ = stack[1].m_obj;
lean_object* v_a_1093_ = stack[2].m_obj;
lean_object* v_a_1094_ = stack[3].m_obj;
lean_object* v_a_1095_ = stack[4].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec_ref(v_x_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1106_, lean_object* v_x_1107_){
_start:
{
switch(lean_obj_tag(v_x_1107_))
{
case 2:
{
lean_object* v_info_1108_; lean_object* v_val_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
v_info_1108_ = lean_ctor_get(v_x_1107_, 0);
v_val_1109_ = lean_ctor_get(v_x_1107_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1111_ = v_x_1107_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_val_1109_);
lean_inc(v_info_1108_);
lean_dec(v_x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_apply_1(v_f_1106_, v_info_1108_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_val_1109_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
case 3:
{
lean_object* v_info_1118_; lean_object* v_rawVal_1119_; lean_object* v_val_1120_; lean_object* v_preresolved_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_info_1118_ = lean_ctor_get(v_x_1107_, 0);
v_rawVal_1119_ = lean_ctor_get(v_x_1107_, 1);
v_val_1120_ = lean_ctor_get(v_x_1107_, 2);
v_preresolved_1121_ = lean_ctor_get(v_x_1107_, 3);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v_x_1107_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_preresolved_1121_);
lean_inc(v_val_1120_);
lean_inc(v_rawVal_1119_);
lean_inc(v_info_1118_);
lean_dec(v_x_1107_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_apply_1(v_f_1106_, v_info_1118_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_rawVal_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_val_1120_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_preresolved_1121_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
case 1:
{
lean_object* v_info_1130_; lean_object* v_kind_1131_; lean_object* v_args_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_info_1130_ = lean_ctor_get(v_x_1107_, 0);
v_kind_1131_ = lean_ctor_get(v_x_1107_, 1);
v_args_1132_ = lean_ctor_get(v_x_1107_, 2);
v___x_1133_ = lean_array_get_size(v_args_1132_);
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_nat_sub(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_nat_dec_lt(v___x_1135_, v___x_1133_);
if (v___x_1136_ == 0)
{
lean_dec(v___x_1135_);
lean_dec_ref(v_f_1106_);
return v_x_1107_;
}
else
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1148_; 
lean_inc_ref(v_args_1132_);
lean_inc(v_kind_1131_);
lean_inc(v_info_1130_);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1149_ = lean_ctor_get(v_x_1107_, 2);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_x_1107_, 1);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_x_1107_, 0);
lean_dec(v_unused_1151_);
v___x_1138_ = v_x_1107_;
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v_x_1107_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_v_1140_; lean_object* v___x_1141_; lean_object* v_xs_x27_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v_v_1140_ = lean_array_fget(v_args_1132_, v___x_1135_);
v___x_1141_ = lean_box(0);
v_xs_x27_1142_ = lean_array_fset(v_args_1132_, v___x_1135_, v___x_1141_);
v___x_1143_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1106_, v_v_1140_);
v___x_1144_ = lean_array_fset(v_xs_x27_1142_, v___x_1135_, v___x_1143_);
lean_dec(v___x_1135_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 2, v___x_1144_);
v___x_1146_ = v___x_1138_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_info_1130_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_kind_1131_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1106_);
return v_x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1152_, lean_object* v_x_1153_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
lean_object* v_trailing_1154_; lean_object* v_leading_1155_; lean_object* v_pos_1156_; lean_object* v_endPos_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1174_; 
v_trailing_1154_ = lean_ctor_get(v_x_1153_, 2);
v_leading_1155_ = lean_ctor_get(v_x_1153_, 0);
v_pos_1156_ = lean_ctor_get(v_x_1153_, 1);
v_endPos_1157_ = lean_ctor_get(v_x_1153_, 3);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_x_1153_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1159_ = v_x_1153_;
v_isShared_1160_ = v_isSharedCheck_1174_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_endPos_1157_);
lean_inc(v_trailing_1154_);
lean_inc(v_pos_1156_);
lean_inc(v_leading_1155_);
lean_dec(v_x_1153_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1174_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_str_1161_; lean_object* v_startPos_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_str_1161_ = lean_ctor_get(v_trailing_1154_, 0);
v_startPos_1162_ = lean_ctor_get(v_trailing_1154_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_trailing_1154_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_trailing_1154_, 2);
lean_dec(v_unused_1173_);
v___x_1164_ = v_trailing_1154_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_startPos_1162_);
lean_inc(v_str_1161_);
lean_dec(v_trailing_1154_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 2, v_stopPos_1152_);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_str_1161_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_startPos_1162_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_stopPos_1152_);
v___x_1167_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 2, v___x_1167_);
v___x_1169_ = v___x_1159_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_leading_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_pos_1156_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_endPos_1157_);
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
}
else
{
lean_dec(v_stopPos_1152_);
return v_x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1175_, lean_object* v_x_1176_){
_start:
{
switch(lean_obj_tag(v_x_1176_))
{
case 2:
{
lean_object* v_info_1177_; lean_object* v_val_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
v_info_1177_ = lean_ctor_get(v_x_1176_, 0);
v_val_1178_ = lean_ctor_get(v_x_1176_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v_x_1176_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_val_1178_);
lean_inc(v_info_1177_);
lean_dec(v_x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1175_, v_info_1177_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_val_1178_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
case 3:
{
lean_object* v_info_1187_; lean_object* v_rawVal_1188_; lean_object* v_val_1189_; lean_object* v_preresolved_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_info_1187_ = lean_ctor_get(v_x_1176_, 0);
v_rawVal_1188_ = lean_ctor_get(v_x_1176_, 1);
v_val_1189_ = lean_ctor_get(v_x_1176_, 2);
v_preresolved_1190_ = lean_ctor_get(v_x_1176_, 3);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v_x_1176_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_preresolved_1190_);
lean_inc(v_val_1189_);
lean_inc(v_rawVal_1188_);
lean_inc(v_info_1187_);
lean_dec(v_x_1176_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1175_, v_info_1187_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_rawVal_1188_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_val_1189_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_preresolved_1190_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
case 1:
{
lean_object* v_info_1199_; lean_object* v_kind_1200_; lean_object* v_args_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_info_1199_ = lean_ctor_get(v_x_1176_, 0);
v_kind_1200_ = lean_ctor_get(v_x_1176_, 1);
v_args_1201_ = lean_ctor_get(v_x_1176_, 2);
v___x_1202_ = lean_array_get_size(v_args_1201_);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = lean_nat_sub(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_nat_dec_lt(v___x_1204_, v___x_1202_);
if (v___x_1205_ == 0)
{
lean_dec(v___x_1204_);
lean_dec(v_stopPos_1175_);
return v_x_1176_;
}
else
{
lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1217_; 
lean_inc_ref(v_args_1201_);
lean_inc(v_kind_1200_);
lean_inc(v_info_1199_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; 
v_unused_1218_ = lean_ctor_get(v_x_1176_, 2);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_x_1176_, 1);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_x_1176_, 0);
lean_dec(v_unused_1220_);
v___x_1207_ = v_x_1176_;
v_isShared_1208_ = v_isSharedCheck_1217_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v_x_1176_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1217_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_v_1209_; lean_object* v___x_1210_; lean_object* v_xs_x27_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v_v_1209_ = lean_array_fget(v_args_1201_, v___x_1204_);
v___x_1210_ = lean_box(0);
v_xs_x27_1211_ = lean_array_fset(v_args_1201_, v___x_1204_, v___x_1210_);
v___x_1212_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1175_, v_v_1209_);
v___x_1213_ = lean_array_fset(v_xs_x27_1211_, v___x_1204_, v___x_1212_);
lean_dec(v___x_1204_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 2, v___x_1213_);
v___x_1215_ = v___x_1207_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_info_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_kind_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1175_);
return v_x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1221_, lean_object* v_c_1222_, lean_object* v_s_1223_){
_start:
{
lean_object* v_s_1224_; lean_object* v_stxStack_1225_; lean_object* v_pos_1226_; lean_object* v_tail_1227_; lean_object* v_s_1228_; lean_object* v_tail_1229_; lean_object* v___x_1230_; 
v_s_1224_ = lean_apply_2(v_p_1221_, v_c_1222_, v_s_1223_);
v_stxStack_1225_ = lean_ctor_get(v_s_1224_, 0);
lean_inc_ref(v_stxStack_1225_);
v_pos_1226_ = lean_ctor_get(v_s_1224_, 2);
lean_inc(v_pos_1226_);
v_tail_1227_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1225_);
lean_dec_ref(v_stxStack_1225_);
v_s_1228_ = l_Lean_Parser_ParserState_popSyntax(v_s_1224_);
v_tail_1229_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1226_, v_tail_1227_);
v___x_1230_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1228_, v_tail_1229_);
return v___x_1230_;
}
}
lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1232_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailing_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1233_;
v_res_1233_ = l_Lake_Toml_trailing_formatter___redArg();
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1235_;
}
}
lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1242_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailing_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1236_ = stack[0].m_obj;
lean_object* v_a_1237_ = stack[1].m_obj;
lean_object* v_a_1238_ = stack[2].m_obj;
lean_object* v_a_1239_ = stack[3].m_obj;
lean_object* v_a_1240_ = stack[4].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l_Lake_Toml_trailing_formatter(v_p_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lake_Toml_trailing_formatter(v_p_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec_ref(v_p_1244_);
return v_res_1250_;
}
}
lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1252_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailing_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1253_;
v_res_1253_ = l_Lake_Toml_trailing_parenthesizer___redArg();
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1255_;
}
}
lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1262_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailing_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1256_ = stack[0].m_obj;
lean_object* v_a_1257_ = stack[1].m_obj;
lean_object* v_a_1258_ = stack[2].m_obj;
lean_object* v_a_1259_ = stack[3].m_obj;
lean_object* v_a_1260_ = stack[4].m_obj;
lean_object* v_res_1263_;
v_res_1263_ = l_Lake_Toml_trailing_parenthesizer(v_p_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
stack->m_obj
 = v_res_1263_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lake_Toml_trailing_parenthesizer(v_p_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec_ref(v_p_1264_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1272_, 0, v_p_1271_);
v___x_1273_ = l_Lean_Parser_epsilonInfo;
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_p_1275_);
return v___x_1277_;
}
}
lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1279_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_Syntax_getKind(v_a_1284_);
v___x_1286_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1285_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v___x_1286_;
}
}
LEAN_EXPORT void l_Lake_Toml_dynamicNode_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1278_ = stack[0].m_obj;
lean_object* v_a_1279_ = stack[1].m_obj;
lean_object* v_a_1280_ = stack[2].m_obj;
lean_object* v_a_1281_ = stack[3].m_obj;
lean_object* v_res_1287_;
v_res_1287_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
stack->m_obj
 = v_res_1287_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
return v_res_1293_;
}
}
lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT void l_Lake_Toml_dynamicNode_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1294_ = stack[0].m_obj;
lean_object* v_a_1295_ = stack[1].m_obj;
lean_object* v_a_1296_ = stack[2].m_obj;
lean_object* v_a_1297_ = stack[3].m_obj;
lean_object* v_a_1298_ = stack[4].m_obj;
lean_object* v_res_1301_;
v_res_1301_ = l_Lake_Toml_dynamicNode_formatter(v_x_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
stack->m_obj
 = v_res_1301_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lake_Toml_dynamicNode_formatter(v_x_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_x_1302_);
return v_res_1308_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_stxTrav_1312_; lean_object* v_cur_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_st_ref_get(v___y_1309_);
v_stxTrav_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc_ref(v_stxTrav_1312_);
lean_dec(v___x_1311_);
v_cur_1313_ = lean_ctor_get(v_stxTrav_1312_, 0);
lean_inc(v_cur_1313_);
lean_dec_ref(v_stxTrav_1312_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_cur_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1309_ = stack[0].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1309_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1316_);
lean_dec(v___y_1316_);
return v_res_1318_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1320_);
return v___x_1324_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1319_ = stack[0].m_obj;
lean_object* v___y_1320_ = stack[1].m_obj;
lean_object* v___y_1321_ = stack[2].m_obj;
lean_object* v___y_1322_ = stack[3].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
stack->m_obj
 = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1331_;
}
}
lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1337_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1333_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Lean_Syntax_getKind(v_a_1338_);
v___x_1340_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1339_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
return v___x_1340_;
}
}
LEAN_EXPORT void l_Lake_Toml_dynamicNode_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1332_ = stack[0].m_obj;
lean_object* v_a_1333_ = stack[1].m_obj;
lean_object* v_a_1334_ = stack[2].m_obj;
lean_object* v_a_1335_ = stack[3].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
return v_res_1347_;
}
}
lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lake_Toml_dynamicNode_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1348_ = stack[0].m_obj;
lean_object* v_a_1349_ = stack[1].m_obj;
lean_object* v_a_1350_ = stack[2].m_obj;
lean_object* v_a_1351_ = stack[3].m_obj;
lean_object* v_a_1352_ = stack[4].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec_ref(v_x_1356_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_fn_1369_; lean_object* v___x_1370_; 
lean_inc_ref(v_f_1363_);
v___x_1366_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1366_, 0, v_f_1363_);
v___x_1367_ = l_Lake_Toml_dynamicNode(v___x_1366_);
v___x_1368_ = lean_apply_1(v_f_1363_, v___x_1367_);
v_fn_1369_ = lean_ctor_get(v___x_1368_, 1);
lean_inc_ref(v_fn_1369_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = lean_apply_2(v_fn_1369_, v_a_1364_, v_a_1365_);
return v___x_1370_;
}
}
lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNode_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1371_ = stack[0].m_obj;
lean_object* v_a_1372_ = stack[1].m_obj;
lean_object* v_a_1373_ = stack[2].m_obj;
lean_object* v_a_1374_ = stack[3].m_obj;
lean_object* v_res_1377_;
v_res_1377_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
stack->m_obj
 = v_res_1377_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
return v_res_1383_;
}
}
lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNode_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1384_ = stack[0].m_obj;
lean_object* v_a_1385_ = stack[1].m_obj;
lean_object* v_a_1386_ = stack[2].m_obj;
lean_object* v_a_1387_ = stack[3].m_obj;
lean_object* v_a_1388_ = stack[4].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l_Lake_Toml_recNode_formatter(v_f_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lake_Toml_recNode_formatter(v_f_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec_ref(v_f_1392_);
return v_res_1398_;
}
}
lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNode_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1399_ = stack[0].m_obj;
lean_object* v_a_1400_ = stack[1].m_obj;
lean_object* v_a_1401_ = stack[2].m_obj;
lean_object* v_a_1402_ = stack[3].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1411_;
}
}
lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNode_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1412_ = stack[0].m_obj;
lean_object* v_a_1413_ = stack[1].m_obj;
lean_object* v_a_1414_ = stack[2].m_obj;
lean_object* v_a_1415_ = stack[3].m_obj;
lean_object* v_a_1416_ = stack[4].m_obj;
lean_object* v_res_1419_;
v_res_1419_ = l_Lake_Toml_recNode_parenthesizer(v_f_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
stack->m_obj
 = v_res_1419_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lake_Toml_recNode_parenthesizer(v_f_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec_ref(v_f_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1428_, 0, v_f_1427_);
v___x_1429_ = l_Lake_Toml_dynamicNode(v___x_1428_);
return v___x_1429_;
}
}
lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1430_, lean_object* v_kind_1431_, lean_object* v_f_1432_, uint8_t v_anonymous_1433_, lean_object* v_p_1434_){
_start:
{
uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1435_ = 1;
lean_inc(v_kind_1431_);
v___x_1436_ = l_Lean_Parser_mkAntiquot(v_name_1430_, v_kind_1431_, v_anonymous_1433_, v___x_1435_);
v___x_1437_ = lean_apply_1(v_f_1432_, v_p_1434_);
v___x_1438_ = l_Lean_Parser_withAntiquot(v___x_1436_, v___x_1437_);
v___x_1439_ = l_Lean_Parser_withCache(v_kind_1431_, v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1430_ = stack[0].m_obj;
lean_object* v_kind_1431_ = stack[1].m_obj;
lean_object* v_f_1432_ = stack[2].m_obj;
uint8_t v_anonymous_1433_ = stack[3].m_num;
lean_object* v_p_1434_ = stack[4].m_obj;
lean_object* v_res_1440_;
v_res_1440_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1430_, v_kind_1431_, v_f_1432_, v_anonymous_1433_, v_p_1434_);
stack->m_obj
 = v_res_1440_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1441_, lean_object* v_kind_1442_, lean_object* v_f_1443_, lean_object* v_anonymous_1444_, lean_object* v_p_1445_){
_start:
{
uint8_t v_anonymous_boxed_1446_; lean_object* v_res_1447_; 
v_anonymous_boxed_1446_ = lean_unbox(v_anonymous_1444_);
v_res_1447_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1441_, v_kind_1442_, v_f_1443_, v_anonymous_boxed_1446_, v_p_1445_);
return v_res_1447_;
}
}
lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1448_, lean_object* v_kind_1449_, lean_object* v_f_1450_, uint8_t v_anonymous_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1457_ = 1;
v___x_1458_ = lean_box(v_anonymous_1451_);
v___x_1459_ = lean_box(v___x_1457_);
lean_inc(v_kind_1449_);
lean_inc_ref(v_name_1448_);
v___x_1460_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1460_, 0, v_name_1448_);
lean_closure_set(v___x_1460_, 1, v_kind_1449_);
lean_closure_set(v___x_1460_, 2, v___x_1458_);
lean_closure_set(v___x_1460_, 3, v___x_1459_);
v___x_1461_ = lean_box(v_anonymous_1451_);
v___x_1462_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1462_, 0, v_name_1448_);
lean_closure_set(v___x_1462_, 1, v_kind_1449_);
lean_closure_set(v___x_1462_, 2, v_f_1450_);
lean_closure_set(v___x_1462_, 3, v___x_1461_);
v___x_1463_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1460_, v___x_1463_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
return v___x_1464_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNodeWithAntiquot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1448_ = stack[0].m_obj;
lean_object* v_kind_1449_ = stack[1].m_obj;
lean_object* v_f_1450_ = stack[2].m_obj;
uint8_t v_anonymous_1451_ = stack[3].m_num;
lean_object* v_a_1452_ = stack[4].m_obj;
lean_object* v_a_1453_ = stack[5].m_obj;
lean_object* v_a_1454_ = stack[6].m_obj;
lean_object* v_a_1455_ = stack[7].m_obj;
lean_object* v_res_1465_;
v_res_1465_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1448_, v_kind_1449_, v_f_1450_, v_anonymous_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
stack->m_obj
 = v_res_1465_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1466_, lean_object* v_kind_1467_, lean_object* v_f_1468_, lean_object* v_anonymous_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
uint8_t v_anonymous_boxed_1475_; lean_object* v_res_1476_; 
v_anonymous_boxed_1475_ = lean_unbox(v_anonymous_1469_);
v_res_1476_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1466_, v_kind_1467_, v_f_1468_, v_anonymous_boxed_1475_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1476_;
}
}
lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1477_, lean_object* v_kind_1478_, lean_object* v_f_1479_, uint8_t v_anonymous_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1486_ = 1;
v___x_1487_ = lean_box(v_anonymous_1480_);
v___x_1488_ = lean_box(v___x_1486_);
lean_inc(v_kind_1478_);
lean_inc_ref(v_name_1477_);
v___x_1489_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1489_, 0, v_name_1477_);
lean_closure_set(v___x_1489_, 1, v_kind_1478_);
lean_closure_set(v___x_1489_, 2, v___x_1487_);
lean_closure_set(v___x_1489_, 3, v___x_1488_);
v___x_1490_ = lean_box(v_anonymous_1480_);
v___x_1491_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1491_, 0, v_name_1477_);
lean_closure_set(v___x_1491_, 1, v_kind_1478_);
lean_closure_set(v___x_1491_, 2, v_f_1479_);
lean_closure_set(v___x_1491_, 3, v___x_1490_);
v___x_1492_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1492_, 0, v___x_1491_);
v___x_1493_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1489_, v___x_1492_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
return v___x_1493_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNodeWithAntiquot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1477_ = stack[0].m_obj;
lean_object* v_kind_1478_ = stack[1].m_obj;
lean_object* v_f_1479_ = stack[2].m_obj;
uint8_t v_anonymous_1480_ = stack[3].m_num;
lean_object* v_a_1481_ = stack[4].m_obj;
lean_object* v_a_1482_ = stack[5].m_obj;
lean_object* v_a_1483_ = stack[6].m_obj;
lean_object* v_a_1484_ = stack[7].m_obj;
lean_object* v_res_1494_;
v_res_1494_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1477_, v_kind_1478_, v_f_1479_, v_anonymous_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
stack->m_obj
 = v_res_1494_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1495_, lean_object* v_kind_1496_, lean_object* v_f_1497_, lean_object* v_anonymous_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
uint8_t v_anonymous_boxed_1504_; lean_object* v_res_1505_; 
v_anonymous_boxed_1504_ = lean_unbox(v_anonymous_1498_);
v_res_1505_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1495_, v_kind_1496_, v_f_1497_, v_anonymous_boxed_1504_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1505_;
}
}
lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1506_, lean_object* v_kind_1507_, lean_object* v_f_1508_, uint8_t v_anonymous_1509_){
_start:
{
uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1510_ = 1;
lean_inc_n(v_kind_1507_, 2);
lean_inc_ref(v_name_1506_);
v___x_1511_ = l_Lean_Parser_mkAntiquot(v_name_1506_, v_kind_1507_, v_anonymous_1509_, v___x_1510_);
v___x_1512_ = lean_box(v_anonymous_1509_);
v___x_1513_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1513_, 0, v_name_1506_);
lean_closure_set(v___x_1513_, 1, v_kind_1507_);
lean_closure_set(v___x_1513_, 2, v_f_1508_);
lean_closure_set(v___x_1513_, 3, v___x_1512_);
v___x_1514_ = l_Lake_Toml_recNode(v___x_1513_);
v___x_1515_ = l_Lean_Parser_withAntiquot(v___x_1511_, v___x_1514_);
v___x_1516_ = l_Lean_Parser_withCache(v_kind_1507_, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT void l_Lake_Toml_recNodeWithAntiquot_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1506_ = stack[0].m_obj;
lean_object* v_kind_1507_ = stack[1].m_obj;
lean_object* v_f_1508_ = stack[2].m_obj;
uint8_t v_anonymous_1509_ = stack[3].m_num;
lean_object* v_res_1517_;
v_res_1517_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1506_, v_kind_1507_, v_f_1508_, v_anonymous_1509_);
stack->m_obj
 = v_res_1517_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1518_, lean_object* v_kind_1519_, lean_object* v_f_1520_, lean_object* v_anonymous_1521_){
_start:
{
uint8_t v_anonymous_boxed_1522_; lean_object* v_res_1523_; 
v_anonymous_boxed_1522_ = lean_unbox(v_anonymous_1521_);
v_res_1523_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1518_, v_kind_1519_, v_f_1520_, v_anonymous_boxed_1522_);
return v_res_1523_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___f_1531_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1532_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1533_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1533_, 0, v___x_1532_);
lean_closure_set(v___x_1533_, 1, v___f_1531_);
return v___x_1533_;
}
}
lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1541_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1542_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1542_, 0, v___x_1540_);
lean_closure_set(v___x_1542_, 1, v_p_1534_);
lean_closure_set(v___x_1542_, 2, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1544_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1542_, v___x_1543_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
return v___x_1544_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepByLinebreak_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1534_ = stack[0].m_obj;
lean_object* v_a_1535_ = stack[1].m_obj;
lean_object* v_a_1536_ = stack[2].m_obj;
lean_object* v_a_1537_ = stack[3].m_obj;
lean_object* v_a_1538_ = stack[4].m_obj;
lean_object* v_res_1545_;
v_res_1545_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
stack->m_obj
 = v_res_1545_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
return v_res_1552_;
}
}
lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1553_, uint8_t v_allowTrailingLinebreak_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1553_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepByLinebreak_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1553_ = stack[0].m_obj;
uint8_t v_allowTrailingLinebreak_1554_ = stack[1].m_num;
lean_object* v_a_1555_ = stack[2].m_obj;
lean_object* v_a_1556_ = stack[3].m_obj;
lean_object* v_a_1557_ = stack[4].m_obj;
lean_object* v_a_1558_ = stack[5].m_obj;
lean_object* v_res_1561_;
v_res_1561_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1553_, v_allowTrailingLinebreak_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
stack->m_obj
 = v_res_1561_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1562_, lean_object* v_allowTrailingLinebreak_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1569_; lean_object* v_res_1570_; 
v_allowTrailingLinebreak_boxed_1569_ = lean_unbox(v_allowTrailingLinebreak_1563_);
v_res_1570_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1562_, v_allowTrailingLinebreak_boxed_1569_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
return v_res_1570_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___f_1574_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1575_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1576_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1576_, 0, v___x_1575_);
lean_closure_set(v___x_1576_, 1, v___f_1574_);
return v___x_1576_;
}
}
lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1583_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1584_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1585_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1585_, 0, v___x_1583_);
lean_closure_set(v___x_1585_, 1, v_p_1577_);
lean_closure_set(v___x_1585_, 2, v___x_1584_);
v___x_1586_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1587_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1585_, v___x_1586_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1587_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepByLinebreak_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1577_ = stack[0].m_obj;
lean_object* v_a_1578_ = stack[1].m_obj;
lean_object* v_a_1579_ = stack[2].m_obj;
lean_object* v_a_1580_ = stack[3].m_obj;
lean_object* v_a_1581_ = stack[4].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
return v_res_1595_;
}
}
lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1596_, uint8_t v_allowTrailingLinebreak_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1596_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepByLinebreak_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1596_ = stack[0].m_obj;
uint8_t v_allowTrailingLinebreak_1597_ = stack[1].m_num;
lean_object* v_a_1598_ = stack[2].m_obj;
lean_object* v_a_1599_ = stack[3].m_obj;
lean_object* v_a_1600_ = stack[4].m_obj;
lean_object* v_a_1601_ = stack[5].m_obj;
lean_object* v_res_1604_;
v_res_1604_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1596_, v_allowTrailingLinebreak_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
stack->m_obj
 = v_res_1604_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1605_, lean_object* v_allowTrailingLinebreak_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1612_; lean_object* v_res_1613_; 
v_allowTrailingLinebreak_boxed_1612_ = lean_unbox(v_allowTrailingLinebreak_1606_);
v_res_1613_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1605_, v_allowTrailingLinebreak_boxed_1612_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
return v_res_1613_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1615_ = l_Lean_Parser_symbol(v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1618_ = l_Lean_Parser_checkLinebreakBefore(v___x_1617_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = l_Lean_Parser_pushNone;
v___x_1620_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1621_ = l_Lean_Parser_andthen(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1622_, uint8_t v_allowTrailingLinebreak_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_p_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1624_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1625_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1626_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1624_, v_p_1622_, v___x_1625_);
v___x_1627_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1628_ = l_Lean_Parser_sepByNoAntiquot(v_p_1626_, v___x_1627_, v_allowTrailingLinebreak_1623_);
return v___x_1628_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepByLinebreak_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1622_ = stack[0].m_obj;
uint8_t v_allowTrailingLinebreak_1623_ = stack[1].m_num;
lean_object* v_res_1629_;
v_res_1629_ = l_Lake_Toml_sepByLinebreak(v_p_1622_, v_allowTrailingLinebreak_1623_);
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1630_, lean_object* v_allowTrailingLinebreak_1631_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1632_; lean_object* v_res_1633_; 
v_allowTrailingLinebreak_boxed_1632_ = lean_unbox(v_allowTrailingLinebreak_1631_);
v_res_1633_ = l_Lake_Toml_sepByLinebreak(v_p_1630_, v_allowTrailingLinebreak_boxed_1632_);
return v_res_1633_;
}
}
lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1640_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1641_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1642_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1642_, 0, v___x_1640_);
lean_closure_set(v___x_1642_, 1, v_p_1634_);
lean_closure_set(v___x_1642_, 2, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1644_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1642_, v___x_1643_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1644_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepBy1Linebreak_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1634_ = stack[0].m_obj;
lean_object* v_a_1635_ = stack[1].m_obj;
lean_object* v_a_1636_ = stack[2].m_obj;
lean_object* v_a_1637_ = stack[3].m_obj;
lean_object* v_a_1638_ = stack[4].m_obj;
lean_object* v_res_1645_;
v_res_1645_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
stack->m_obj
 = v_res_1645_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1652_;
}
}
lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1653_, uint8_t v_allowTrailingLinebreak_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1653_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepBy1Linebreak_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1653_ = stack[0].m_obj;
uint8_t v_allowTrailingLinebreak_1654_ = stack[1].m_num;
lean_object* v_a_1655_ = stack[2].m_obj;
lean_object* v_a_1656_ = stack[3].m_obj;
lean_object* v_a_1657_ = stack[4].m_obj;
lean_object* v_a_1658_ = stack[5].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1653_, v_allowTrailingLinebreak_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1662_, lean_object* v_allowTrailingLinebreak_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1669_; lean_object* v_res_1670_; 
v_allowTrailingLinebreak_boxed_1669_ = lean_unbox(v_allowTrailingLinebreak_1663_);
v_res_1670_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1662_, v_allowTrailingLinebreak_boxed_1669_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
return v_res_1670_;
}
}
lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1677_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1678_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1679_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1679_, 0, v___x_1677_);
lean_closure_set(v___x_1679_, 1, v_p_1671_);
lean_closure_set(v___x_1679_, 2, v___x_1678_);
v___x_1680_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1681_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1679_, v___x_1680_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1681_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1671_ = stack[0].m_obj;
lean_object* v_a_1672_ = stack[1].m_obj;
lean_object* v_a_1673_ = stack[2].m_obj;
lean_object* v_a_1674_ = stack[3].m_obj;
lean_object* v_a_1675_ = stack[4].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1689_;
}
}
lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1690_, uint8_t v_allowTrailingLinebreak_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1690_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepBy1Linebreak_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1690_ = stack[0].m_obj;
uint8_t v_allowTrailingLinebreak_1691_ = stack[1].m_num;
lean_object* v_a_1692_ = stack[2].m_obj;
lean_object* v_a_1693_ = stack[3].m_obj;
lean_object* v_a_1694_ = stack[4].m_obj;
lean_object* v_a_1695_ = stack[5].m_obj;
lean_object* v_res_1698_;
v_res_1698_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1690_, v_allowTrailingLinebreak_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
stack->m_obj
 = v_res_1698_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1699_, lean_object* v_allowTrailingLinebreak_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1706_; lean_object* v_res_1707_; 
v_allowTrailingLinebreak_boxed_1706_ = lean_unbox(v_allowTrailingLinebreak_1700_);
v_res_1707_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1699_, v_allowTrailingLinebreak_boxed_1706_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1707_;
}
}
lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1708_, uint8_t v_allowTrailingLinebreak_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_p_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1710_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1711_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1712_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1710_, v_p_1708_, v___x_1711_);
v___x_1713_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1714_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1712_, v___x_1713_, v_allowTrailingLinebreak_1709_);
return v___x_1714_;
}
}
LEAN_EXPORT void l_Lake_Toml_sepBy1Linebreak_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1708_ = stack[0].m_obj;
uint8_t v_allowTrailingLinebreak_1709_ = stack[1].m_num;
lean_object* v_res_1715_;
v_res_1715_ = l_Lake_Toml_sepBy1Linebreak(v_p_1708_, v_allowTrailingLinebreak_1709_);
stack->m_obj
 = v_res_1715_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1716_, lean_object* v_allowTrailingLinebreak_1717_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1718_; lean_object* v_res_1719_; 
v_allowTrailingLinebreak_boxed_1718_ = lean_unbox(v_allowTrailingLinebreak_1717_);
v_res_1719_ = l_Lake_Toml_sepBy1Linebreak(v_p_1716_, v_allowTrailingLinebreak_boxed_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1720_, lean_object* v_c_1721_, lean_object* v_s_1722_){
_start:
{
lean_object* v_toCacheableParserContext_1723_; lean_object* v_quotDepth_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_toCacheableParserContext_1723_ = lean_ctor_get(v_c_1721_, 2);
v_quotDepth_1724_ = lean_ctor_get(v_toCacheableParserContext_1723_, 1);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_nat_dec_lt(v___x_1725_, v_quotDepth_1724_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_apply_2(v_p_1720_, v_c_1721_, v_s_1722_);
return v___x_1727_;
}
else
{
lean_dec_ref(v_c_1721_);
lean_dec_ref(v_p_1720_);
return v_s_1722_;
}
}
}
lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
lean_inc(v_a_1732_);
lean_inc_ref(v_a_1731_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
v___x_1734_ = lean_apply_5(v_p_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, lean_box(0));
return v___x_1734_;
}
}
LEAN_EXPORT void l_Lake_Toml_skipInsideQuot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1728_ = stack[0].m_obj;
lean_object* v_a_1729_ = stack[1].m_obj;
lean_object* v_a_1730_ = stack[2].m_obj;
lean_object* v_a_1731_ = stack[3].m_obj;
lean_object* v_a_1732_ = stack[4].m_obj;
lean_object* v_res_1735_;
v_res_1735_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
stack->m_obj
 = v_res_1735_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
return v_res_1742_;
}
}
lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; 
lean_inc(v_a_1747_);
lean_inc_ref(v_a_1746_);
lean_inc(v_a_1745_);
lean_inc_ref(v_a_1744_);
v___x_1749_ = lean_apply_5(v_p_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, lean_box(0));
return v___x_1749_;
}
}
LEAN_EXPORT void l_Lake_Toml_skipInsideQuot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1743_ = stack[0].m_obj;
lean_object* v_a_1744_ = stack[1].m_obj;
lean_object* v_a_1745_ = stack[2].m_obj;
lean_object* v_a_1746_ = stack[3].m_obj;
lean_object* v_a_1747_ = stack[4].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
stack->m_obj
 = v_res_1750_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1758_){
_start:
{
lean_object* v_info_1759_; lean_object* v_fn_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v_info_1759_ = lean_ctor_get(v_p_1758_, 0);
v_fn_1760_ = lean_ctor_get(v_p_1758_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_p_1758_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v_p_1758_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_fn_1760_);
lean_inc(v_info_1759_);
lean_dec(v_p_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1764_, 0, v_fn_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_info_1759_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
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
