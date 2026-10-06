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
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_430_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
lean_ctor_set(v___x_433_, 3, v___x_432_);
lean_ctor_set(v___x_433_, 4, v___x_431_);
lean_ctor_set(v___x_433_, 5, v___x_431_);
lean_ctor_set(v___x_433_, 6, v___x_431_);
lean_ctor_set(v___x_433_, 7, v___x_431_);
lean_ctor_set(v___x_433_, 8, v___x_431_);
lean_ctor_set(v___x_433_, 9, v___x_431_);
lean_ctor_set(v___x_433_, 10, v___x_431_);
lean_ctor_set(v___x_433_, 11, v___x_430_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_unsigned_to_nat(32u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4(void){
_start:
{
size_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_437_ = ((size_t)5ULL);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_unsigned_to_nat(32u);
v___x_440_ = lean_mk_empty_array_with_capacity(v___x_439_);
v___x_441_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3);
v___x_442_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_438_);
lean_ctor_set(v___x_442_, 3, v___x_438_);
lean_ctor_set_usize(v___x_442_, 4, v___x_437_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_box(1);
v___x_444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4);
v___x_445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(lean_object* v_msgData_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; lean_object* v_toCold_452_; lean_object* v_env_453_; lean_object* v_options_454_; uint8_t v___x_455_; lean_object* v_env_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_451_ = lean_st_ref_get(v___y_449_);
v_toCold_452_ = lean_ctor_get(v___y_448_, 0);
v_env_453_ = lean_ctor_get(v___x_451_, 0);
lean_inc_ref(v_env_453_);
lean_dec(v___x_451_);
v_options_454_ = lean_ctor_get(v_toCold_452_, 2);
v___x_455_ = 0;
v_env_456_ = l_Lean_Environment_setRecordingDeps(v_env_453_, v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
v___x_458_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
lean_inc_ref(v_options_454_);
v___x_459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_459_, 0, v_env_456_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
lean_ctor_set(v___x_459_, 2, v___x_458_);
lean_ctor_set(v___x_459_, 3, v_options_454_);
v___x_460_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v_msgData_447_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(lean_object* v_msgData_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_466_;
}
}
static double _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_467_; double v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_float_of_nat(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(lean_object* v_cls_471_, lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_ref_476_; lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_523_; 
v_ref_476_ = lean_ctor_get(v___y_473_, 2);
v___x_477_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_472_, v___y_473_, v___y_474_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_523_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_523_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_523_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v_traceState_483_; lean_object* v_env_484_; lean_object* v_nextMacroScope_485_; lean_object* v_ngen_486_; lean_object* v_auxDeclNGen_487_; lean_object* v_cache_488_; lean_object* v_recordedDeps_489_; lean_object* v_messages_490_; lean_object* v_infoState_491_; lean_object* v_snapshotTasks_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_522_; 
v___x_482_ = lean_st_ref_take(v___y_474_);
v_traceState_483_ = lean_ctor_get(v___x_482_, 4);
v_env_484_ = lean_ctor_get(v___x_482_, 0);
v_nextMacroScope_485_ = lean_ctor_get(v___x_482_, 1);
v_ngen_486_ = lean_ctor_get(v___x_482_, 2);
v_auxDeclNGen_487_ = lean_ctor_get(v___x_482_, 3);
v_cache_488_ = lean_ctor_get(v___x_482_, 5);
v_recordedDeps_489_ = lean_ctor_get(v___x_482_, 6);
v_messages_490_ = lean_ctor_get(v___x_482_, 7);
v_infoState_491_ = lean_ctor_get(v___x_482_, 8);
v_snapshotTasks_492_ = lean_ctor_get(v___x_482_, 9);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_522_ == 0)
{
v___x_494_ = v___x_482_;
v_isShared_495_ = v_isSharedCheck_522_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snapshotTasks_492_);
lean_inc(v_infoState_491_);
lean_inc(v_messages_490_);
lean_inc(v_recordedDeps_489_);
lean_inc(v_cache_488_);
lean_inc(v_traceState_483_);
lean_inc(v_auxDeclNGen_487_);
lean_inc(v_ngen_486_);
lean_inc(v_nextMacroScope_485_);
lean_inc(v_env_484_);
lean_dec(v___x_482_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_522_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
uint64_t v_tid_496_; lean_object* v_traces_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_521_; 
v_tid_496_ = lean_ctor_get_uint64(v_traceState_483_, sizeof(void*)*1);
v_traces_497_ = lean_ctor_get(v_traceState_483_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_traceState_483_);
if (v_isSharedCheck_521_ == 0)
{
v___x_499_ = v_traceState_483_;
v_isShared_500_ = v_isSharedCheck_521_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_traces_497_);
lean_dec(v_traceState_483_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_521_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; double v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_box(0);
v___x_503_ = lean_float_once(&l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
v___x_504_ = 0;
v___x_505_ = ((lean_object*)(l_Lake_Toml_mkUnexpectedCharError___closed__1));
v___x_506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_506_, 0, v_cls_471_);
lean_ctor_set(v___x_506_, 1, v___x_502_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
lean_ctor_set_float(v___x_506_, sizeof(void*)*3, v___x_503_);
lean_ctor_set_float(v___x_506_, sizeof(void*)*3 + 8, v___x_503_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*3 + 16, v___x_504_);
v___x_507_ = ((lean_object*)(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1));
v___x_508_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v_a_478_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
lean_inc(v_ref_476_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_ref_476_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_PersistentArray_push___redArg(v_traces_497_, v___x_509_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_510_);
v___x_512_ = v___x_499_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_510_);
lean_ctor_set_uint64(v_reuseFailAlloc_520_, sizeof(void*)*1, v_tid_496_);
v___x_512_ = v_reuseFailAlloc_520_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 4, v___x_512_);
v___x_514_ = v___x_494_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_env_484_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_nextMacroScope_485_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_ngen_486_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_auxDeclNGen_487_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_519_, 5, v_cache_488_);
lean_ctor_set(v_reuseFailAlloc_519_, 6, v_recordedDeps_489_);
lean_ctor_set(v_reuseFailAlloc_519_, 7, v_messages_490_);
lean_ctor_set(v_reuseFailAlloc_519_, 8, v_infoState_491_);
lean_ctor_set(v_reuseFailAlloc_519_, 9, v_snapshotTasks_492_);
v___x_514_ = v_reuseFailAlloc_519_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_st_ref_put(v___y_474_, v___x_514_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_501_);
v___x_517_ = v___x_480_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_501_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(lean_object* v_cls_524_, lean_object* v_msg_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_524_, v_msg_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_529_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__6(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_541_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__5));
v___x_542_ = l_Lean_Name_append(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__8(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__7));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lake_Toml_atom_formatter___redArg___closed__10(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__9));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg(lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; lean_object* v_a_555_; 
v___x_554_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_550_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref(v___x_554_);
if (lean_obj_tag(v_a_555_) == 2)
{
lean_object* v_info_556_; lean_object* v_val_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_info_556_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_info_556_);
v_val_557_ = lean_ctor_get(v_a_555_, 1);
lean_inc_ref(v_val_557_);
v___x_558_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_555_);
lean_dec_ref_known(v_a_555_, 2);
v___x_559_ = 0;
v___x_560_ = lean_box(v___x_559_);
v___x_561_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(v___x_561_, 0, v_info_556_);
lean_closure_set(v___x_561_, 1, v_val_557_);
lean_closure_set(v___x_561_, 2, v___x_560_);
v___x_562_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(v___x_558_, v___x_561_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v___x_558_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
lean_dec_ref_known(v___x_562_, 1);
v___x_563_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_550_);
return v___x_563_;
}
else
{
return v___x_562_;
}
}
else
{
lean_object* v_toCold_564_; lean_object* v_options_565_; uint8_t v_hasTrace_566_; 
v_toCold_564_ = lean_ctor_get(v_a_551_, 0);
v_options_565_ = lean_ctor_get(v_toCold_564_, 2);
v_hasTrace_566_ = lean_ctor_get_uint8(v_options_565_, sizeof(void*)*1);
if (v_hasTrace_566_ == 0)
{
lean_object* v___x_567_; 
lean_dec(v_a_555_);
v___x_567_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_567_;
}
else
{
lean_object* v_inheritedTraceOptions_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_inheritedTraceOptions_568_ = lean_ctor_get(v_toCold_564_, 11);
v___x_569_ = ((lean_object*)(l_Lake_Toml_atom_formatter___redArg___closed__3));
v___x_570_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__6, &l_Lake_Toml_atom_formatter___redArg___closed__6_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__6);
v___x_571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_568_, v_options_565_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec(v_a_555_);
v___x_572_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_573_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__8, &l_Lake_Toml_atom_formatter___redArg___closed__8_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__8);
v___x_574_ = lean_box(0);
v___x_575_ = 0;
v___x_576_ = l_Lean_Syntax_formatStx(v_a_555_, v___x_574_, v___x_575_);
v___x_577_ = l_Lean_MessageData_ofFormat(v___x_576_);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_573_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_obj_once(&l_Lake_Toml_atom_formatter___redArg___closed__10, &l_Lake_Toml_atom_formatter___redArg___closed__10_once, _init_l_Lake_Toml_atom_formatter___redArg___closed__10);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v___x_569_, v___x_580_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_582_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
return v___x_582_;
}
else
{
return v___x_581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___redArg___boxed(lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lake_Toml_atom_formatter___redArg(v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter(lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lake_Toml_atom_formatter___redArg(v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_atom_formatter___boxed(lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lake_Toml_atom_formatter(v_x_597_, v_x_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec_ref(v_x_598_);
lean_dec_ref(v_x_597_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(lean_object* v_cls_605_, lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(v_cls_605_, v_msg_606_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(lean_object* v_cls_613_, lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(v_cls_613_, v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_624_);
lean_dec(v_a_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_630_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(v_x_635_, v_x_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec_ref(v_x_636_);
lean_dec_ref(v_x_635_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom(uint32_t v_c_643_, lean_object* v_expected_644_, lean_object* v_trailingFn_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_box_uint32(v_c_643_);
v___x_647_ = lean_alloc_closure((void*)(l_Lake_Toml_chFn___boxed), 4, 2);
lean_closure_set(v___x_647_, 0, v___x_646_);
lean_closure_set(v___x_647_, 1, v_expected_644_);
v___x_648_ = l_Lake_Toml_atom(v___x_647_, v_trailingFn_645_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom___boxed(lean_object* v_c_649_, lean_object* v_expected_650_, lean_object* v_trailingFn_651_){
_start:
{
uint32_t v_c_boxed_652_; lean_object* v_res_653_; 
v_c_boxed_652_ = lean_unbox_uint32(v_c_649_);
lean_dec(v_c_649_);
v_res_653_ = l_Lake_Toml_chAtom(v_c_boxed_652_, v_expected_650_, v_trailingFn_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg(uint32_t v_c_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
uint8_t v___x_660_; lean_object* v___x_661_; 
v___x_660_ = 0;
v___x_661_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(v_c_654_, v___x_660_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___redArg___boxed(lean_object* v_c_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
uint32_t v_c_boxed_668_; lean_object* v_res_669_; 
v_c_boxed_668_ = lean_unbox_uint32(v_c_662_);
lean_dec(v_c_662_);
v_res_669_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_boxed_668_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter(uint32_t v_c_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lake_Toml_chAtom_formatter___redArg(v_c_670_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object* v_c_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
uint32_t v_c_boxed_687_; lean_object* v_res_688_; 
v_c_boxed_687_ = lean_unbox_uint32(v_c_679_);
lean_dec(v_c_679_);
v_res_688_ = l_Lake_Toml_chAtom_formatter(v_c_boxed_687_, v_x_680_, v_x_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec_ref(v_x_681_);
lean_dec(v_x_680_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg(lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_692_);
lean_dec(v_a_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer(uint32_t v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_699_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
uint32_t v_x_19__boxed_712_; lean_object* v_res_713_; 
v_x_19__boxed_712_ = lean_unbox_uint32(v_x_704_);
lean_dec(v_x_704_);
v_res_713_ = l_Lake_Toml_chAtom_parenthesizer(v_x_19__boxed_712_, v_x_705_, v_x_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec_ref(v_x_706_);
lean_dec(v_x_705_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom(lean_object* v_s_714_, lean_object* v_expected_715_, lean_object* v_trailingFn_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_str_721_; lean_object* v_startInclusive_722_; lean_object* v_endExclusive_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_string_utf8_byte_size(v_s_714_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_s_714_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
v___x_720_ = l_String_Slice_trimAscii(v___x_719_);
v_str_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc_ref(v_str_721_);
v_startInclusive_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_startInclusive_722_);
v_endExclusive_723_ = lean_ctor_get(v___x_720_, 2);
lean_inc(v_endExclusive_723_);
lean_dec_ref(v___x_720_);
v___x_724_ = lean_string_utf8_extract_fast(v_str_721_, v_startInclusive_722_, v_endExclusive_723_);
lean_dec(v_endExclusive_723_);
lean_dec(v_startInclusive_722_);
lean_dec_ref(v_str_721_);
v___x_725_ = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(v___x_725_, 0, v___x_724_);
lean_closure_set(v___x_725_, 1, v_expected_715_);
v___x_726_ = l_Lake_Toml_atom(v___x_725_, v_trailingFn_716_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg(lean_object* v_s_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___redArg___boxed(lean_object* v_s_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lake_Toml_strAtom_formatter___redArg(v_s_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter(lean_object* v_s_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_s_741_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_formatter___boxed(lean_object* v_s_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lake_Toml_strAtom_formatter(v_s_750_, v_x_751_, v_x_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec_ref(v_x_752_);
lean_dec(v_x_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg(lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_762_);
lean_dec(v_a_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_769_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_strAtom_parenthesizer___boxed(lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lake_Toml_strAtom_parenthesizer(v_x_774_, v_x_775_, v_x_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec_ref(v_x_776_);
lean_dec(v_x_775_);
lean_dec_ref(v_x_774_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_pushLit(lean_object* v_kind_783_, lean_object* v_startPos_784_, lean_object* v_trailingFn_785_, lean_object* v_c_786_, lean_object* v_s_787_){
_start:
{
lean_object* v_toInputContext_788_; lean_object* v_pos_789_; lean_object* v_inputString_790_; lean_object* v_endPos_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_809_; 
v_toInputContext_788_ = lean_ctor_get(v_c_786_, 0);
lean_inc_ref(v_toInputContext_788_);
v_pos_789_ = lean_ctor_get(v_s_787_, 2);
lean_inc(v_pos_789_);
v_inputString_790_ = lean_ctor_get(v_toInputContext_788_, 0);
v_endPos_791_ = lean_ctor_get(v_toInputContext_788_, 3);
v_isSharedCheck_809_ = !lean_is_exclusive(v_toInputContext_788_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_810_ = lean_ctor_get(v_toInputContext_788_, 2);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_toInputContext_788_, 1);
lean_dec(v_unused_811_);
v___x_793_ = v_toInputContext_788_;
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_endPos_791_);
lean_inc(v_inputString_790_);
lean_dec(v_toInputContext_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_leading_795_; lean_object* v_s_796_; lean_object* v_pos_797_; lean_object* v_val_798_; lean_object* v___y_800_; uint8_t v___x_806_; 
lean_inc(v_startPos_784_);
v_leading_795_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_786_, v_startPos_784_);
v_s_796_ = lean_apply_2(v_trailingFn_785_, v_c_786_, v_s_787_);
v_pos_797_ = lean_ctor_get(v_s_796_, 2);
lean_inc(v_pos_797_);
v_val_798_ = lean_string_utf8_extract(v_inputString_790_, v_startPos_784_, v_pos_789_);
v___x_806_ = lean_nat_dec_le(v_pos_797_, v_endPos_791_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v_pos_797_);
lean_inc(v_pos_789_);
v___x_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_807_, 0, v_inputString_790_);
lean_ctor_set(v___x_807_, 1, v_pos_789_);
lean_ctor_set(v___x_807_, 2, v_endPos_791_);
v___y_800_ = v___x_807_;
goto v___jp_799_;
}
else
{
lean_object* v___x_808_; 
lean_dec(v_endPos_791_);
lean_inc(v_pos_789_);
v___x_808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_808_, 0, v_inputString_790_);
lean_ctor_set(v___x_808_, 1, v_pos_789_);
lean_ctor_set(v___x_808_, 2, v_pos_797_);
v___y_800_ = v___x_808_;
goto v___jp_799_;
}
v___jp_799_:
{
lean_object* v_info_802_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 3, v_pos_789_);
lean_ctor_set(v___x_793_, 2, v___y_800_);
lean_ctor_set(v___x_793_, 1, v_startPos_784_);
lean_ctor_set(v___x_793_, 0, v_leading_795_);
v_info_802_ = v___x_793_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_leading_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_startPos_784_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v___y_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_pos_789_);
v_info_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = l_Lean_Syntax_mkLit(v_kind_783_, v_val_798_, v_info_802_);
v___x_804_ = l_Lean_Parser_ParserState_pushSyntax(v_s_796_, v___x_803_);
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litFn(lean_object* v_kind_812_, lean_object* v_p_813_, lean_object* v_trailingFn_814_, lean_object* v_c_815_, lean_object* v_s_816_){
_start:
{
lean_object* v_pos_817_; lean_object* v_s_818_; lean_object* v_errorMsg_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_pos_817_ = lean_ctor_get(v_s_816_, 2);
lean_inc(v_pos_817_);
lean_inc_ref(v_c_815_);
v_s_818_ = lean_apply_2(v_p_813_, v_c_815_, v_s_816_);
v_errorMsg_819_ = lean_ctor_get(v_s_818_, 4);
lean_inc(v_errorMsg_819_);
v___x_820_ = lean_box(0);
v___x_821_ = l_instBEqOption_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_819_, v___x_820_);
lean_dec(v_errorMsg_819_);
if (v___x_821_ == 0)
{
lean_dec(v_pos_817_);
lean_dec_ref(v_c_815_);
lean_dec_ref(v_trailingFn_814_);
lean_dec(v_kind_812_);
return v_s_818_;
}
else
{
lean_object* v___x_822_; 
v___x_822_ = l_Lake_Toml_pushLit(v_kind_812_, v_pos_817_, v_trailingFn_814_, v_c_815_, v_s_818_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit(lean_object* v_kind_823_, lean_object* v_p_824_, lean_object* v_trailingFn_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_827_ = lean_alloc_closure((void*)(l_Lake_Toml_litFn), 5, 3);
lean_closure_set(v___x_827_, 0, v_kind_823_);
lean_closure_set(v___x_827_, 1, v_p_824_);
lean_closure_set(v___x_827_, 2, v_trailingFn_825_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg(lean_object* v_kind_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___redArg___boxed(lean_object* v_kind_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_Toml_lit_formatter___redArg(v_kind_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter(lean_object* v_kind_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_843_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_formatter___boxed(lean_object* v_kind_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lake_Toml_lit_formatter(v_kind_852_, v_x_853_, v_x_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec_ref(v_x_854_);
lean_dec_ref(v_x_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg(lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___redArg___boxed(lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_864_);
lean_dec(v_a_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer(lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_871_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_lit_parenthesizer___boxed(lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lake_Toml_lit_parenthesizer(v_x_876_, v_x_877_, v_x_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_x_878_);
lean_dec_ref(v_x_877_);
lean_dec(v_x_876_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(lean_object* v_kind_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v_kind_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(lean_object* v_kind_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(v_kind_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object* v_name_899_, lean_object* v_kind_900_, uint8_t v_anonymous_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___f_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc(v_kind_900_);
v___f_907_ = lean_alloc_closure((void*)(l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_907_, 0, v_kind_900_);
v___x_908_ = 0;
v___x_909_ = lean_box(v_anonymous_901_);
v___x_910_ = lean_box(v___x_908_);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_911_, 0, v_name_899_);
lean_closure_set(v___x_911_, 1, v_kind_900_);
lean_closure_set(v___x_911_, 2, v___x_909_);
lean_closure_set(v___x_911_, 3, v___x_910_);
v___x_912_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_911_, v___f_907_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(lean_object* v_name_913_, lean_object* v_kind_914_, lean_object* v_anonymous_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_anonymous_boxed_921_; lean_object* v_res_922_; 
v_anonymous_boxed_921_ = lean_unbox(v_anonymous_915_);
v_res_922_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_913_, v_kind_914_, v_anonymous_boxed_921_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter(lean_object* v_name_923_, lean_object* v_kind_924_, lean_object* v_p_925_, lean_object* v_trailingFn_926_, uint8_t v_anonymous_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v_name_923_, v_kind_924_, v_anonymous_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_formatter___boxed(lean_object* v_name_934_, lean_object* v_kind_935_, lean_object* v_p_936_, lean_object* v_trailingFn_937_, lean_object* v_anonymous_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_anonymous_boxed_944_; lean_object* v_res_945_; 
v_anonymous_boxed_944_ = lean_unbox(v_anonymous_938_);
v_res_945_ = l_Lake_Toml_litWithAntiquot_formatter(v_name_934_, v_kind_935_, v_p_936_, v_trailingFn_937_, v_anonymous_boxed_944_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec_ref(v_trailingFn_937_);
lean_dec_ref(v_p_936_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_947_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object* v_name_959_, lean_object* v_kind_960_, uint8_t v_anonymous_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___f_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___f_967_ = ((lean_object*)(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0));
v___x_968_ = 0;
v___x_969_ = lean_box(v_anonymous_961_);
v___x_970_ = lean_box(v___x_968_);
v___x_971_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_971_, 0, v_name_959_);
lean_closure_set(v___x_971_, 1, v_kind_960_);
lean_closure_set(v___x_971_, 2, v___x_969_);
lean_closure_set(v___x_971_, 3, v___x_970_);
v___x_972_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_971_, v___f_967_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(lean_object* v_name_973_, lean_object* v_kind_974_, lean_object* v_anonymous_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
uint8_t v_anonymous_boxed_981_; lean_object* v_res_982_; 
v_anonymous_boxed_981_ = lean_unbox(v_anonymous_975_);
v_res_982_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_973_, v_kind_974_, v_anonymous_boxed_981_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer(lean_object* v_name_983_, lean_object* v_kind_984_, lean_object* v_p_985_, lean_object* v_trailingFn_986_, uint8_t v_anonymous_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v_name_983_, v_kind_984_, v_anonymous_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(lean_object* v_name_994_, lean_object* v_kind_995_, lean_object* v_p_996_, lean_object* v_trailingFn_997_, lean_object* v_anonymous_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
uint8_t v_anonymous_boxed_1004_; lean_object* v_res_1005_; 
v_anonymous_boxed_1004_ = lean_unbox(v_anonymous_998_);
v_res_1005_ = l_Lake_Toml_litWithAntiquot_parenthesizer(v_name_994_, v_kind_995_, v_p_996_, v_trailingFn_997_, v_anonymous_boxed_1004_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_trailingFn_997_);
lean_dec_ref(v_p_996_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot(lean_object* v_name_1006_, lean_object* v_kind_1007_, lean_object* v_p_1008_, lean_object* v_trailingFn_1009_, uint8_t v_anonymous_1010_){
_start:
{
uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = 0;
lean_inc(v_kind_1007_);
v___x_1012_ = l_Lean_Parser_mkAntiquot(v_name_1006_, v_kind_1007_, v_anonymous_1010_, v___x_1011_);
v___x_1013_ = l_Lake_Toml_lit(v_kind_1007_, v_p_1008_, v_trailingFn_1009_);
v___x_1014_ = l_Lean_Parser_withAntiquot(v___x_1012_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_litWithAntiquot___boxed(lean_object* v_name_1015_, lean_object* v_kind_1016_, lean_object* v_p_1017_, lean_object* v_trailingFn_1018_, lean_object* v_anonymous_1019_){
_start:
{
uint8_t v_anonymous_boxed_1020_; lean_object* v_res_1021_; 
v_anonymous_boxed_1020_ = lean_unbox(v_anonymous_1019_);
v_res_1021_ = l_Lake_Toml_litWithAntiquot(v_name_1015_, v_kind_1016_, v_p_1017_, v_trailingFn_1018_, v_anonymous_boxed_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon(lean_object* v_fn_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = l_Lean_Parser_epsilonInfo;
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_fn_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg(){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___redArg___boxed(lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lake_Toml_epsilon_formatter___redArg();
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter(lean_object* v_x_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_formatter___boxed(lean_object* v_x_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lake_Toml_epsilon_formatter(v_x_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec_ref(v_x_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer(lean_object* v_x_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_epsilon_parenthesizer___boxed(lean_object* v_x_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lake_Toml_epsilon_parenthesizer(v_x_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec_ref(v_x_1056_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(lean_object* v_f_1063_, lean_object* v_x_1064_){
_start:
{
switch(lean_obj_tag(v_x_1064_))
{
case 2:
{
lean_object* v_info_1065_; lean_object* v_val_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1074_; 
v_info_1065_ = lean_ctor_get(v_x_1064_, 0);
v_val_1066_ = lean_ctor_get(v_x_1064_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1068_ = v_x_1064_;
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_val_1066_);
lean_inc(v_info_1065_);
lean_dec(v_x_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_apply_1(v_f_1063_, v_info_1065_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_val_1066_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
case 3:
{
lean_object* v_info_1075_; lean_object* v_rawVal_1076_; lean_object* v_val_1077_; lean_object* v_preresolved_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_info_1075_ = lean_ctor_get(v_x_1064_, 0);
v_rawVal_1076_ = lean_ctor_get(v_x_1064_, 1);
v_val_1077_ = lean_ctor_get(v_x_1064_, 2);
v_preresolved_1078_ = lean_ctor_get(v_x_1064_, 3);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v_x_1064_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_preresolved_1078_);
lean_inc(v_val_1077_);
lean_inc(v_rawVal_1076_);
lean_inc(v_info_1075_);
lean_dec(v_x_1064_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_apply_1(v_f_1063_, v_info_1075_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_rawVal_1076_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_val_1077_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_preresolved_1078_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
case 1:
{
lean_object* v_info_1087_; lean_object* v_kind_1088_; lean_object* v_args_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_info_1087_ = lean_ctor_get(v_x_1064_, 0);
v_kind_1088_ = lean_ctor_get(v_x_1064_, 1);
v_args_1089_ = lean_ctor_get(v_x_1064_, 2);
v___x_1090_ = lean_array_get_size(v_args_1089_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_sub(v___x_1090_, v___x_1091_);
v___x_1093_ = lean_nat_dec_lt(v___x_1092_, v___x_1090_);
if (v___x_1093_ == 0)
{
lean_dec(v___x_1092_);
lean_dec_ref(v_f_1063_);
return v_x_1064_;
}
else
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1105_; 
lean_inc_ref(v_args_1089_);
lean_inc(v_kind_1088_);
lean_inc(v_info_1087_);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; lean_object* v_unused_1107_; lean_object* v_unused_1108_; 
v_unused_1106_ = lean_ctor_get(v_x_1064_, 2);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_x_1064_, 1);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_x_1064_, 0);
lean_dec(v_unused_1108_);
v___x_1095_ = v_x_1064_;
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v_x_1064_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1105_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_v_1097_; lean_object* v___x_1098_; lean_object* v_xs_x27_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v_v_1097_ = lean_array_fget(v_args_1089_, v___x_1092_);
v___x_1098_ = lean_box(0);
v_xs_x27_1099_ = lean_array_fset(v_args_1089_, v___x_1092_, v___x_1098_);
v___x_1100_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(v_f_1063_, v_v_1097_);
v___x_1101_ = lean_array_fset(v_xs_x27_1099_, v___x_1092_, v___x_1100_);
lean_dec(v___x_1092_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 2, v___x_1101_);
v___x_1103_ = v___x_1095_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_info_1087_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_kind_1088_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
default: 
{
lean_dec_ref(v_f_1063_);
return v_x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(lean_object* v_stopPos_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_object* v_trailing_1111_; lean_object* v_leading_1112_; lean_object* v_pos_1113_; lean_object* v_endPos_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1131_; 
v_trailing_1111_ = lean_ctor_get(v_x_1110_, 2);
v_leading_1112_ = lean_ctor_get(v_x_1110_, 0);
v_pos_1113_ = lean_ctor_get(v_x_1110_, 1);
v_endPos_1114_ = lean_ctor_get(v_x_1110_, 3);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1116_ = v_x_1110_;
v_isShared_1117_ = v_isSharedCheck_1131_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_endPos_1114_);
lean_inc(v_trailing_1111_);
lean_inc(v_pos_1113_);
lean_inc(v_leading_1112_);
lean_dec(v_x_1110_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1131_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_str_1118_; lean_object* v_startPos_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1129_; 
v_str_1118_ = lean_ctor_get(v_trailing_1111_, 0);
v_startPos_1119_ = lean_ctor_get(v_trailing_1111_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_trailing_1111_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v_trailing_1111_, 2);
lean_dec(v_unused_1130_);
v___x_1121_ = v_trailing_1111_;
v_isShared_1122_ = v_isSharedCheck_1129_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_startPos_1119_);
lean_inc(v_str_1118_);
lean_dec(v_trailing_1111_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1129_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 2, v_stopPos_1109_);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_str_1118_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_startPos_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_stopPos_1109_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 2, v___x_1124_);
v___x_1126_ = v___x_1116_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_leading_1112_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_pos_1113_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_endPos_1114_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
else
{
lean_dec(v_stopPos_1109_);
return v_x_1110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(lean_object* v_stopPos_1132_, lean_object* v_x_1133_){
_start:
{
switch(lean_obj_tag(v_x_1133_))
{
case 2:
{
lean_object* v_info_1134_; lean_object* v_val_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_info_1134_ = lean_ctor_get(v_x_1133_, 0);
v_val_1135_ = lean_ctor_get(v_x_1133_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v_x_1133_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_val_1135_);
lean_inc(v_info_1134_);
lean_dec(v_x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1132_, v_info_1134_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_val_1135_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
case 3:
{
lean_object* v_info_1144_; lean_object* v_rawVal_1145_; lean_object* v_val_1146_; lean_object* v_preresolved_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_info_1144_ = lean_ctor_get(v_x_1133_, 0);
v_rawVal_1145_ = lean_ctor_get(v_x_1133_, 1);
v_val_1146_ = lean_ctor_get(v_x_1133_, 2);
v_preresolved_1147_ = lean_ctor_get(v_x_1133_, 3);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v_x_1133_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_preresolved_1147_);
lean_inc(v_val_1146_);
lean_inc(v_rawVal_1145_);
lean_inc(v_info_1144_);
lean_dec(v_x_1133_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_1132_, v_info_1144_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_rawVal_1145_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_val_1146_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_preresolved_1147_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
case 1:
{
lean_object* v_info_1156_; lean_object* v_kind_1157_; lean_object* v_args_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_info_1156_ = lean_ctor_get(v_x_1133_, 0);
v_kind_1157_ = lean_ctor_get(v_x_1133_, 1);
v_args_1158_ = lean_ctor_get(v_x_1133_, 2);
v___x_1159_ = lean_array_get_size(v_args_1158_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_sub(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_nat_dec_lt(v___x_1161_, v___x_1159_);
if (v___x_1162_ == 0)
{
lean_dec(v___x_1161_);
lean_dec(v_stopPos_1132_);
return v_x_1133_;
}
else
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
lean_inc_ref(v_args_1158_);
lean_inc(v_kind_1157_);
lean_inc(v_info_1156_);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1175_ = lean_ctor_get(v_x_1133_, 2);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_x_1133_, 1);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_x_1133_, 0);
lean_dec(v_unused_1177_);
v___x_1164_ = v_x_1133_;
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v_x_1133_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_v_1166_; lean_object* v___x_1167_; lean_object* v_xs_x27_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v_v_1166_ = lean_array_fget(v_args_1158_, v___x_1161_);
v___x_1167_ = lean_box(0);
v_xs_x27_1168_ = lean_array_fset(v_args_1158_, v___x_1161_, v___x_1167_);
v___x_1169_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_1132_, v_v_1166_);
v___x_1170_ = lean_array_fset(v_xs_x27_1168_, v___x_1161_, v___x_1169_);
lean_dec(v___x_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 2, v___x_1170_);
v___x_1172_ = v___x_1164_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_info_1156_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_kind_1157_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
default: 
{
lean_dec(v_stopPos_1132_);
return v_x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_extendTrailingFn(lean_object* v_p_1178_, lean_object* v_c_1179_, lean_object* v_s_1180_){
_start:
{
lean_object* v_s_1181_; lean_object* v_stxStack_1182_; lean_object* v_pos_1183_; lean_object* v_tail_1184_; lean_object* v_s_1185_; lean_object* v_tail_1186_; lean_object* v___x_1187_; 
v_s_1181_ = lean_apply_2(v_p_1178_, v_c_1179_, v_s_1180_);
v_stxStack_1182_ = lean_ctor_get(v_s_1181_, 0);
lean_inc_ref(v_stxStack_1182_);
v_pos_1183_ = lean_ctor_get(v_s_1181_, 2);
lean_inc(v_pos_1183_);
v_tail_1184_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1182_);
lean_dec_ref(v_stxStack_1182_);
v_s_1185_ = l_Lean_Parser_ParserState_popSyntax(v_s_1181_);
v_tail_1186_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_1183_, v_tail_1184_);
v___x_1187_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1185_, v_tail_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg(){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___redArg___boxed(lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lake_Toml_trailing_formatter___redArg();
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter(lean_object* v_p_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_formatter___boxed(lean_object* v_p_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lake_Toml_trailing_formatter(v_p_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec_ref(v_p_1199_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg(){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___redArg___boxed(lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lake_Toml_trailing_parenthesizer___redArg();
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer(lean_object* v_p_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing_parenthesizer___boxed(lean_object* v_p_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lake_Toml_trailing_parenthesizer(v_p_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v_p_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailing(lean_object* v_p_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_alloc_closure((void*)(l_Lake_Toml_extendTrailingFn), 3, 1);
lean_closure_set(v___x_1225_, 0, v_p_1224_);
v___x_1226_ = l_Lean_Parser_epsilonInfo;
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode(lean_object* v_p_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lake_Toml_atom___closed__2));
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_p_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg(lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(v_a_1232_);
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = l_Lean_Syntax_getKind(v_a_1237_);
v___x_1239_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(v___x_1238_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___redArg___boxed(lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter(lean_object* v_x_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_formatter___boxed(lean_object* v_x_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lake_Toml_dynamicNode_formatter(v_x_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v_x_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v_stxTrav_1263_; lean_object* v_cur_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_st_ref_get(v___y_1260_);
v_stxTrav_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_stxTrav_1263_);
lean_dec(v___x_1262_);
v_cur_1264_ = lean_ctor_get(v_stxTrav_1263_, 0);
lean_inc(v_cur_1264_);
lean_dec_ref(v_stxTrav_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_cur_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1266_);
lean_dec(v___y_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_1270_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg(lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_1282_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = l_Lean_Syntax_getKind(v_a_1287_);
v___x_1289_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(v___x_1288_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer(lean_object* v_x_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dynamicNode_parenthesizer___boxed(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lake_Toml_dynamicNode_parenthesizer(v_x_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec_ref(v_x_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(lean_object* v_f_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_fn_1316_; lean_object* v___x_1317_; 
lean_inc_ref(v_f_1310_);
v___x_1313_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1313_, 0, v_f_1310_);
v___x_1314_ = l_Lake_Toml_dynamicNode(v___x_1313_);
v___x_1315_ = lean_apply_1(v_f_1310_, v___x_1314_);
v_fn_1316_ = lean_ctor_get(v___x_1315_, 1);
lean_inc_ref(v_fn_1316_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = lean_apply_2(v_fn_1316_, v_a_1311_, v_a_1312_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg(lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___redArg___boxed(lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lake_Toml_recNode_formatter___redArg(v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter(lean_object* v_f_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lake_Toml_dynamicNode_formatter___redArg(v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_formatter___boxed(lean_object* v_f_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lake_Toml_recNode_formatter(v_f_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec_ref(v_f_1337_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg(lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___redArg___boxed(lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lake_Toml_recNode_parenthesizer___redArg(v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer(lean_object* v_f_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode_parenthesizer___boxed(lean_object* v_f_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lake_Toml_recNode_parenthesizer(v_f_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_f_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNode(lean_object* v_f_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn), 3, 1);
lean_closure_set(v___x_1371_, 0, v_f_1370_);
v___x_1372_ = l_Lake_Toml_dynamicNode(v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(lean_object* v_name_1373_, lean_object* v_kind_1374_, lean_object* v_f_1375_, uint8_t v_anonymous_1376_, lean_object* v_p_1377_){
_start:
{
uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1378_ = 1;
lean_inc(v_kind_1374_);
v___x_1379_ = l_Lean_Parser_mkAntiquot(v_name_1373_, v_kind_1374_, v_anonymous_1376_, v___x_1378_);
v___x_1380_ = lean_apply_1(v_f_1375_, v_p_1377_);
v___x_1381_ = l_Lean_Parser_withAntiquot(v___x_1379_, v___x_1380_);
v___x_1382_ = l_Lean_Parser_withCache(v_kind_1374_, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(lean_object* v_name_1383_, lean_object* v_kind_1384_, lean_object* v_f_1385_, lean_object* v_anonymous_1386_, lean_object* v_p_1387_){
_start:
{
uint8_t v_anonymous_boxed_1388_; lean_object* v_res_1389_; 
v_anonymous_boxed_1388_ = lean_unbox(v_anonymous_1386_);
v_res_1389_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(v_name_1383_, v_kind_1384_, v_f_1385_, v_anonymous_boxed_1388_, v_p_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object* v_name_1390_, lean_object* v_kind_1391_, lean_object* v_f_1392_, uint8_t v_anonymous_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1399_ = 1;
v___x_1400_ = lean_box(v_anonymous_1393_);
v___x_1401_ = lean_box(v___x_1399_);
lean_inc(v_kind_1391_);
lean_inc_ref(v_name_1390_);
v___x_1402_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_1402_, 0, v_name_1390_);
lean_closure_set(v___x_1402_, 1, v_kind_1391_);
lean_closure_set(v___x_1402_, 2, v___x_1400_);
lean_closure_set(v___x_1402_, 3, v___x_1401_);
v___x_1403_ = lean_box(v_anonymous_1393_);
v___x_1404_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1404_, 0, v_name_1390_);
lean_closure_set(v___x_1404_, 1, v_kind_1391_);
lean_closure_set(v___x_1404_, 2, v_f_1392_);
lean_closure_set(v___x_1404_, 3, v___x_1403_);
v___x_1405_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_formatter___boxed), 6, 1);
lean_closure_set(v___x_1405_, 0, v___x_1404_);
v___x_1406_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1402_, v___x_1405_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(lean_object* v_name_1407_, lean_object* v_kind_1408_, lean_object* v_f_1409_, lean_object* v_anonymous_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
uint8_t v_anonymous_boxed_1416_; lean_object* v_res_1417_; 
v_anonymous_boxed_1416_ = lean_unbox(v_anonymous_1410_);
v_res_1417_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v_name_1407_, v_kind_1408_, v_f_1409_, v_anonymous_boxed_1416_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object* v_name_1418_, lean_object* v_kind_1419_, lean_object* v_f_1420_, uint8_t v_anonymous_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1427_ = 1;
v___x_1428_ = lean_box(v_anonymous_1421_);
v___x_1429_ = lean_box(v___x_1427_);
lean_inc(v_kind_1419_);
lean_inc_ref(v_name_1418_);
v___x_1430_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_1430_, 0, v_name_1418_);
lean_closure_set(v___x_1430_, 1, v_kind_1419_);
lean_closure_set(v___x_1430_, 2, v___x_1428_);
lean_closure_set(v___x_1430_, 3, v___x_1429_);
v___x_1431_ = lean_box(v_anonymous_1421_);
v___x_1432_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1432_, 0, v_name_1418_);
lean_closure_set(v___x_1432_, 1, v_kind_1419_);
lean_closure_set(v___x_1432_, 2, v_f_1420_);
lean_closure_set(v___x_1432_, 3, v___x_1431_);
v___x_1433_ = lean_alloc_closure((void*)(l_Lake_Toml_recNode_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1430_, v___x_1433_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_1435_, lean_object* v_kind_1436_, lean_object* v_f_1437_, lean_object* v_anonymous_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
uint8_t v_anonymous_boxed_1444_; lean_object* v_res_1445_; 
v_anonymous_boxed_1444_ = lean_unbox(v_anonymous_1438_);
v_res_1445_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v_name_1435_, v_kind_1436_, v_f_1437_, v_anonymous_boxed_1444_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object* v_name_1446_, lean_object* v_kind_1447_, lean_object* v_f_1448_, uint8_t v_anonymous_1449_){
_start:
{
uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1450_ = 1;
lean_inc_n(v_kind_1447_, 2);
lean_inc_ref(v_name_1446_);
v___x_1451_ = l_Lean_Parser_mkAntiquot(v_name_1446_, v_kind_1447_, v_anonymous_1449_, v___x_1450_);
v___x_1452_ = lean_box(v_anonymous_1449_);
v___x_1453_ = lean_alloc_closure((void*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed), 5, 4);
lean_closure_set(v___x_1453_, 0, v_name_1446_);
lean_closure_set(v___x_1453_, 1, v_kind_1447_);
lean_closure_set(v___x_1453_, 2, v_f_1448_);
lean_closure_set(v___x_1453_, 3, v___x_1452_);
v___x_1454_ = l_Lake_Toml_recNode(v___x_1453_);
v___x_1455_ = l_Lean_Parser_withAntiquot(v___x_1451_, v___x_1454_);
v___x_1456_ = l_Lean_Parser_withCache(v_kind_1447_, v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_recNodeWithAntiquot___boxed(lean_object* v_name_1457_, lean_object* v_kind_1458_, lean_object* v_f_1459_, lean_object* v_anonymous_1460_){
_start:
{
uint8_t v_anonymous_boxed_1461_; lean_object* v_res_1462_; 
v_anonymous_boxed_1461_ = lean_unbox(v_anonymous_1460_);
v_res_1462_ = l_Lake_Toml_recNodeWithAntiquot(v_name_1457_, v_kind_1458_, v_f_1459_, v_anonymous_boxed_1461_);
return v_res_1462_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5(void){
_start:
{
lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___f_1470_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0));
v___x_1471_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
v___x_1472_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1472_, 0, v___x_1471_);
lean_closure_set(v___x_1472_, 1, v___f_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg(lean_object* v_p_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1479_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1480_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1481_, 0, v___x_1479_);
lean_closure_set(v___x_1481_, 1, v_p_1473_);
lean_closure_set(v___x_1481_, 2, v___x_1480_);
v___x_1482_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1483_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1481_, v___x_1482_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(lean_object* v_p_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter(lean_object* v_p_1491_, uint8_t v_allowTrailingLinebreak_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(v_p_1491_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object* v_p_1499_, lean_object* v_allowTrailingLinebreak_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1506_; lean_object* v_res_1507_; 
v_allowTrailingLinebreak_boxed_1506_ = lean_unbox(v_allowTrailingLinebreak_1500_);
v_res_1507_ = l_Lake_Toml_sepByLinebreak_formatter(v_p_1499_, v_allowTrailingLinebreak_boxed_1506_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1507_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2(void){
_start:
{
lean_object* v___f_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___f_1511_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0));
v___x_1512_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_1513_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1513_, 0, v___x_1512_);
lean_closure_set(v___x_1513_, 1, v___f_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(lean_object* v_p_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1520_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1521_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1522_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1522_, 0, v___x_1520_);
lean_closure_set(v___x_1522_, 1, v_p_1514_);
lean_closure_set(v___x_1522_, 2, v___x_1521_);
v___x_1523_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1524_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1522_, v___x_1523_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(lean_object* v_p_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer(lean_object* v_p_1532_, uint8_t v_allowTrailingLinebreak_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(v_p_1532_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object* v_p_1540_, lean_object* v_allowTrailingLinebreak_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1547_; lean_object* v_res_1548_; 
v_allowTrailingLinebreak_boxed_1547_ = lean_unbox(v_allowTrailingLinebreak_1541_);
v_res_1548_ = l_Lake_Toml_sepByLinebreak_parenthesizer(v_p_1540_, v_allowTrailingLinebreak_boxed_1547_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
return v_res_1548_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__0(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3));
v___x_1550_ = l_Lean_Parser_symbol(v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__2(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak___closed__1));
v___x_1553_ = l_Lean_Parser_checkLinebreakBefore(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lake_Toml_sepByLinebreak___closed__3(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = l_Lean_Parser_pushNone;
v___x_1555_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__2, &l_Lake_Toml_sepByLinebreak___closed__2_once, _init_l_Lake_Toml_sepByLinebreak___closed__2);
v___x_1556_ = l_Lean_Parser_andthen(v___x_1555_, v___x_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak(lean_object* v_p_1557_, uint8_t v_allowTrailingLinebreak_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_p_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1559_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1560_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1561_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1559_, v_p_1557_, v___x_1560_);
v___x_1562_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1563_ = l_Lean_Parser_sepByNoAntiquot(v_p_1561_, v___x_1562_, v_allowTrailingLinebreak_1558_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepByLinebreak___boxed(lean_object* v_p_1564_, lean_object* v_allowTrailingLinebreak_1565_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1566_; lean_object* v_res_1567_; 
v_allowTrailingLinebreak_boxed_1566_ = lean_unbox(v_allowTrailingLinebreak_1565_);
v_res_1567_ = l_Lake_Toml_sepByLinebreak(v_p_1564_, v_allowTrailingLinebreak_boxed_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg(lean_object* v_p_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1574_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1575_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4));
v___x_1576_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1576_, 0, v___x_1574_);
lean_closure_set(v___x_1576_, 1, v_p_1568_);
lean_closure_set(v___x_1576_, 2, v___x_1575_);
v___x_1577_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5, &l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once, _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5);
v___x_1578_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1576_, v___x_1577_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(lean_object* v_p_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter(lean_object* v_p_1586_, uint8_t v_allowTrailingLinebreak_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(v_p_1586_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_formatter___boxed(lean_object* v_p_1594_, lean_object* v_allowTrailingLinebreak_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1601_; lean_object* v_res_1602_; 
v_allowTrailingLinebreak_boxed_1601_ = lean_unbox(v_allowTrailingLinebreak_1595_);
v_res_1602_ = l_Lake_Toml_sepBy1Linebreak_formatter(v_p_1594_, v_allowTrailingLinebreak_boxed_1601_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(lean_object* v_p_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1609_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1610_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1));
v___x_1611_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1611_, 0, v___x_1609_);
lean_closure_set(v___x_1611_, 1, v_p_1603_);
lean_closure_set(v___x_1611_, 2, v___x_1610_);
v___x_1612_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2, &l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once, _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2);
v___x_1613_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1611_, v___x_1612_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(lean_object* v_p_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer(lean_object* v_p_1621_, uint8_t v_allowTrailingLinebreak_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(v_p_1621_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(lean_object* v_p_1629_, lean_object* v_allowTrailingLinebreak_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1636_; lean_object* v_res_1637_; 
v_allowTrailingLinebreak_boxed_1636_ = lean_unbox(v_allowTrailingLinebreak_1630_);
v_res_1637_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(v_p_1629_, v_allowTrailingLinebreak_boxed_1636_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak(lean_object* v_p_1638_, uint8_t v_allowTrailingLinebreak_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_p_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1640_ = ((lean_object*)(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2));
v___x_1641_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__0, &l_Lake_Toml_sepByLinebreak___closed__0_once, _init_l_Lake_Toml_sepByLinebreak___closed__0);
v_p_1642_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1640_, v_p_1638_, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lake_Toml_sepByLinebreak___closed__3, &l_Lake_Toml_sepByLinebreak___closed__3_once, _init_l_Lake_Toml_sepByLinebreak___closed__3);
v___x_1644_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1642_, v___x_1643_, v_allowTrailingLinebreak_1639_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_sepBy1Linebreak___boxed(lean_object* v_p_1645_, lean_object* v_allowTrailingLinebreak_1646_){
_start:
{
uint8_t v_allowTrailingLinebreak_boxed_1647_; lean_object* v_res_1648_; 
v_allowTrailingLinebreak_boxed_1647_ = lean_unbox(v_allowTrailingLinebreak_1646_);
v_res_1648_ = l_Lake_Toml_sepBy1Linebreak(v_p_1645_, v_allowTrailingLinebreak_boxed_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuotFn(lean_object* v_p_1649_, lean_object* v_c_1650_, lean_object* v_s_1651_){
_start:
{
lean_object* v_toCacheableParserContext_1652_; lean_object* v_quotDepth_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v_toCacheableParserContext_1652_ = lean_ctor_get(v_c_1650_, 2);
v_quotDepth_1653_ = lean_ctor_get(v_toCacheableParserContext_1652_, 1);
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = lean_nat_dec_lt(v___x_1654_, v_quotDepth_1653_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_apply_2(v_p_1649_, v_c_1650_, v_s_1651_);
return v___x_1656_;
}
else
{
lean_dec_ref(v_c_1650_);
lean_dec_ref(v_p_1649_);
return v_s_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter(lean_object* v_p_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; 
lean_inc(v_a_1661_);
lean_inc_ref(v_a_1660_);
lean_inc(v_a_1659_);
lean_inc_ref(v_a_1658_);
v___x_1663_ = lean_apply_5(v_p_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, lean_box(0));
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_formatter___boxed(lean_object* v_p_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lake_Toml_skipInsideQuot_formatter(v_p_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer(lean_object* v_p_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; 
lean_inc(v_a_1675_);
lean_inc_ref(v_a_1674_);
lean_inc(v_a_1673_);
lean_inc_ref(v_a_1672_);
v___x_1677_ = lean_apply_5(v_p_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, lean_box(0));
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(lean_object* v_p_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lake_Toml_skipInsideQuot_parenthesizer(v_p_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_skipInsideQuot(lean_object* v_p_1685_){
_start:
{
lean_object* v_info_1686_; lean_object* v_fn_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
v_info_1686_ = lean_ctor_get(v_p_1685_, 0);
v_fn_1687_ = lean_ctor_get(v_p_1685_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_p_1685_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1689_ = v_p_1685_;
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_fn_1687_);
lean_inc(v_info_1686_);
lean_dec(v_p_1685_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_alloc_closure((void*)(l_Lake_Toml_skipInsideQuotFn), 3, 1);
lean_closure_set(v___x_1691_, 0, v_fn_1687_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_info_1686_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
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
