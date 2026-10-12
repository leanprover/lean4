// Lean compiler output
// Module: Lean.Parser.Extra
// Imports: public import Lean.PrettyPrinter.Formatter public import Lean.PrettyPrinter.Parenthesizer import all Lean.Parser.Types import all Lean.Parser.Basic import all Lean.Parser.Extension public meta import Lean.Hygiene
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_rawIdentNoAntiquot;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Std_Format_getIndent(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_identNoAntiquot;
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(uint8_t, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_numLitNoAntiquot;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_charLitNoAntiquot;
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fill___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_scientificLitNoAntiquot;
lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hygieneInfoNoAntiquot;
lean_object* l_Lean_Parser_withAntiquotAcceptLhs(lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLitNoAntiquot;
lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
extern lean_object* l_Lean_Parser_hexnumNoAntiquot;
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
extern lean_object* l_Lean_Parser_strLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_termParser_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_termParser_formatter___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Parser_termParser_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_termParser_formatter___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_commandParser_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Parser_commandParser_formatter___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_commandParser_formatter___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Parser_commandParser_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_commandParser_formatter___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Parser_commandParser_formatter___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_commandParser_formatter___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_formatter___redArg___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "antiquotNestedExpr"};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value;
static const lean_ctor_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 217, 111, 200, 191, 162, 168, 125)}};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__2_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value;
static const lean_string_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__4_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 184, 198, 144, 189, 249, 117, 153)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 167, 177, 159, 214, 65, 137, 70)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_antiquotExpr_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_antiquotExpr_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_antiquotExpr_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotExpr_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__2_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 12, 45, 178, 67, 53, 106)}};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__3_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__8_value;
static const lean_string_object l_Lean_Parser_mkAntiquot_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pseudo"};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__9 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__9_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquot_formatter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__9_value),LEAN_SCALAR_PTR_LITERAL(246, 255, 48, 87, 29, 98, 48, 237)}};
static const lean_object* l_Lean_Parser_mkAntiquot_formatter___closed__10 = (const lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 184, 198, 144, 189, 249, 117, 153)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 86, 214, 3, 200, 227, 238, 166)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_antiquotExpr_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotExpr_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_antiquotExpr_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_antiquotExpr_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_mkAntiquot_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquot_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquot_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_mkAntiquot_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_mkAntiquot_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 75, 125, 66, 98, 92, 21, 108)}};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__3_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value;
static const lean_ctor_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__5_value;
static const lean_string_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_sepByElemParser_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_sepByElemParser_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_sepByElemParser_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_sepByElemParser_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_mkAntiquotSplice_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_optional_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_optional_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_optional_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_optional_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_optional_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_optional_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Parser_optional_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_optional_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_optional_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_optional_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_optional_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_optional_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_optional_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_optional___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_optional___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_optional(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_optional_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 167, 191, 130, 216, 220, 182, 40)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 506, .m_capacity = 506, .m_length = 505, .m_data = "The parser `optional(p)`, or `(p)\?`, parses `p` if it succeeds,\notherwise it succeeds with no value.\n\nNote that because `\?` is a legal identifier character, one must write `(p)\?` or `p \?` for\nit to parse correctly. `ident\?` will not work; one must write `(ident)\?` instead.\n\nThis parser has arity 1: it produces a `nullKind` node containing either zero arguments\n(for the `none` case) or the list of arguments produced by `p`.\n(In particular, if `p` has arity 0 then the two cases are not differentiated!)"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_many_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_many_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_many_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_many_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_many_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_many_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_many_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_many_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_many_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_many_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_many_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_sepByElemParser_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_many_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_many_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_many___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_many___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_many(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_many_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 114, 232, 230, 181, 52, 168, 160)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 389, .m_capacity = 389, .m_length = 388, .m_data = "The parser `many(p)`, or `p*`, repeats `p` until it fails, and returns the list of results.\n\nThe argument `p` is \"auto-grouped\", meaning that if the arity is greater than 1 it will be\nautomatically replaced by `group(p)` to ensure that it produces exactly 1 value.\n\nThis parser has arity 1: it produces a `nullKind` node containing one argument for each\ninvocation of `p` (or `group(p)`)."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 61, 196, 93, 201, 246, 193, 192)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 647, .m_capacity = 647, .m_length = 646, .m_data = "The parser `many1(p)`, or `p+`, repeats `p` until it fails, and returns the list of results.\n`p` must succeed at least once, or this parser will fail.\n\nNote that this parser produces the same parse tree as the `many(p)` / `p*` combinator,\nand one matches both `p*` and `p+` using `$[ .. ]*` syntax in a syntax match.\n(There is no `$[ .. ]+` syntax.)\n\nThe argument `p` is \"auto-grouped\", meaning that if the arity is greater than 1 it will be\nautomatically replaced by `group(p)` to ensure that it produces exactly 1 value.\n\nThis parser has arity 1: it produces a `nullKind` node containing one argument for each\ninvocation of `p` (or `group(p)`)."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_ident_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_ident_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ident_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_ident_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_ident_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_ident_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_ident_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_ident_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_ident_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_ident_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_ident_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_ident_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_ident_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_ident___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_ident___closed__0;
static lean_once_cell_t l_Lean_Parser_ident___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_ident___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ident;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_ident_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 242, 101, 31, 193, 156, 127, 171)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 855, .m_capacity = 855, .m_length = 844, .m_data = "The parser `ident` parses a single identifier, possibly with namespaces, such as `foo` or\n`bar.baz`. The identifier must not be a declared token, so for example it will not match `\"def\"`\nbecause `def` is a keyword token. Tokens are implicitly declared by using them in string literals\nin parser declarations, so `syntax foo := \"bla\"` will make `bla` no longer legal as an identifier.\n\nIdentifiers can contain special characters or keywords if they are escaped using the `«»` characters:\n`«def»` is an identifier named `def`, and `«x»` is treated the same as `x`. This is useful for\nusing disallowed characters in identifiers such as `«foo.bar».baz` or `«hello world»`.\n\nThis parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.\nYou can use `TSyntax.getId` to extract the name from the resulting syntax object."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_identWithPartialTrailingDot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "no space before"};
static const lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__0 = (const lean_object*)&l_Lean_Parser_identWithPartialTrailingDot___closed__0_value;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__1;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__2;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__3;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__4;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__5;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__6;
static lean_once_cell_t l_Lean_Parser_identWithPartialTrailingDot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_identWithPartialTrailingDot___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_rawIdent_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_rawIdent_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_rawIdent_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_rawIdent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_rawIdent___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent;
static const lean_string_object l_Lean_Parser_hygieneInfo_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Parser_hygieneInfo_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_hygieneInfo_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Parser_hygieneInfo_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_hygieneInfo_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_hygieneInfo_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_hygieneInfo_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_hygieneInfo_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_hygieneInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hygieneInfo___closed__0;
static lean_once_cell_t l_Lean_Parser_hygieneInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hygieneInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_hygieneInfo_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 96, 174, 177, 221, 86, 223, 51)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1027, .m_capacity = 1027, .m_length = 1025, .m_data = "The parser `hygieneInfo` parses no text, but creates a `hygieneInfoKind` node\ncontaining an anonymous identifier as if it were parsed at the current position.\nThis identifier is modified by syntax quotations to add macro scopes like a regular identifier.\n\nThis is used to implement `have := ...` syntax: the `hygieneInfo` between the `have` and `:=`\ncollects macro scopes, which we can apply to `this` when expanding to `have this := ...`.\nSee [the language reference](lean-manual://section/macro-hygiene) for more information about\nmacro hygiene.\n\nThis is also used to implement cdot functions such as `(1 + ·)`. The opening parenthesis contains\na `hygieneInfo` node as does the cdot, which lets cdot expansion hygienically associate parentheses to cdots.\n\nThis parser has arity 1: it produces a `hygieneInfoKind` node containing an anonymous `Syntax.ident`.\nYou can use `HygieneInfo.mkIdent` to create an `Ident` from the syntax object,\nbut you can also use `TSyntax.getHygieneInfo` to get the raw name from the identifier."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_numLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_numLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_numLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_numLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_numLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_numLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_numLit_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_numLit_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_numLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_numLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_numLit_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_numLit_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_numLit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_numLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_numLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_numLit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_numLit_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_numLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_numLit___closed__0;
static lean_once_cell_t l_Lean_Parser_numLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_numLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_numLit;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "numLit"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 124, 25, 195, 9, 201, 171, 221)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 334, .m_capacity = 334, .m_length = 333, .m_data = "The parser `num` parses a numeric literal in several bases:\n\n* Decimal: `129`\n* Hexadecimal: `0xdeadbeef`\n* Octal: `0o755`\n* Binary: `0b1101`\n\nThis parser has arity 1: it produces a `numLitKind` node containing an atom with the text of the\nliteral.\nYou can use `TSyntax.getNat` to extract the number from the resulting syntax object."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_hexnum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l_Lean_Parser_hexnum___closed__0 = (const lean_object*)&l_Lean_Parser_hexnum___closed__0_value;
static const lean_ctor_object l_Lean_Parser_hexnum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_hexnum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l_Lean_Parser_hexnum___closed__1 = (const lean_object*)&l_Lean_Parser_hexnum___closed__1_value;
static lean_once_cell_t l_Lean_Parser_hexnum___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hexnum___closed__2;
static lean_once_cell_t l_Lean_Parser_hexnum___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_hexnum___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_hexnum;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_hexnum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 234, 249, 199, 49, 244, 72, 166)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 384, .m_capacity = 384, .m_length = 383, .m_data = "The parser `hexnum` parses a hexadecimal numeric literal not containing the `0x` prefix.\n\nIt produces a `hexnumKind` node containing an atom with the text of the\nliteral. This parser is mainly used for creating atoms such `#<hexnum>`. Recall that `hexnum`\nis not a token and this parser must be prefixed by another parser.\n\nFor numerals such as `0xadef100a`, you should use `numLit`."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_scientificLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Parser_scientificLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_scientificLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Parser_scientificLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_scientificLit_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_scientificLit_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_scientificLit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_scientificLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_scientificLit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_scientificLit_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_scientificLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_scientificLit___closed__0;
static lean_once_cell_t l_Lean_Parser_scientificLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_scientificLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "scientificLit"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 25, 249, 160, 8, 56, 13, 159)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 286, .m_capacity = 286, .m_length = 285, .m_data = "The parser `scientific` parses a scientific-notation literal, such as `1.3e-24`.\n\nThis parser has arity 1: it produces a `scientificLitKind` node containing an atom with the text\nof the literal.\nYou can use `TSyntax.getScientific` to extract the parts from the resulting syntax object."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_strLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Parser_strLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_strLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_strLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_strLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Parser_strLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_strLit_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_strLit_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_strLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_strLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_strLit_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_strLit_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_strLit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_strLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_strLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_strLit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_strLit_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_strLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_strLit___closed__0;
static lean_once_cell_t l_Lean_Parser_strLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_strLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_strLit;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strLit"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 157, 94, 66, 135, 29, 115, 44)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 493, .m_capacity = 493, .m_length = 490, .m_data = "The parser `str` parses a string literal, such as `\"foo\"` or `\"\\r\\n\"`. Strings can contain\nC-style escapes like `\\n`, `\\\"`, `\\x00` or `\\u2665`, as well as literal unicode characters like `∈`.\nNewlines in a string are interpreted literally.\n\nThis parser has arity 1: it produces a `strLitKind` node containing an atom with the raw\nliteral (including the quote marks and without interpreting the escapes).\nYou can use `TSyntax.getString` to decode the string from the resulting syntax object."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_charLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Parser_charLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_charLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_charLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_charLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Parser_charLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_charLit_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_charLit_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_charLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_charLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_charLit_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_charLit_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_charLit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_charLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_charLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_charLit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_charLit_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_charLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_charLit___closed__0;
static lean_once_cell_t l_Lean_Parser_charLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_charLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_charLit;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "charLit"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 82, 20, 217, 44, 105, 253, 153)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 603, .m_capacity = 603, .m_length = 594, .m_data = "The parser `char` parses a character literal, such as `'a'` or `'\\n'`. Character literals can\ncontain C-style escapes like `\\n`, `\\\"`, `\\x00` or `\\u2665`, as well as literal unicode characters\nlike `∈`, but must evaluate to a single unicode codepoint, so `'♥'` is allowed but `'❤️'` is not\n(since it is two codepoints but one grapheme cluster).\n\nThis parser has arity 1: it produces a `charLitKind` node containing an atom with the raw\nliteral (including the quote marks and without interpreting the escapes).\nYou can use `TSyntax.getChar` to decode the string from the resulting syntax object."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_nameLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Parser_nameLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_nameLit_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_nameLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_nameLit_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Parser_nameLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_nameLit_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_nameLit_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_nameLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_nameLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_nameLit_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_nameLit_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_nameLit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_nameLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_nameLit_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_nameLit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_nameLit_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_nameLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_nameLit___closed__0;
static lean_once_cell_t l_Lean_Parser_nameLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_nameLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nameLit"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 229, 203, 158, 195, 74, 86, 122)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 339, .m_capacity = 339, .m_length = 338, .m_data = "The parser `name` parses a name literal like `` `foo``. The syntax is the same as for identifiers\n(see `ident`) but with a leading backquote.\n\nThis parser has arity 1: it produces a `nameLitKind` node containing the raw literal\n(including the backquote).\nYou can use `TSyntax.getName` to extract the name from the resulting syntax object."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_group_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_group_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_group_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_group_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_group_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_group_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_group_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_group_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 0, 118, 179, 21, 142, 182, 74)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 322, .m_capacity = 322, .m_length = 321, .m_data = "The parser `group(p)` parses the same thing as `p`, but it wraps the results in a `groupKind`\nnode.\n\nThis parser always has arity 1, even if `p` does not. Parsers like `p*` are automatically\nrewritten to `group(p)*` if `p` does not have arity 1, so that the results from separate invocations\nof `p` can be differentiated."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_many1Indent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Parser_many1Indent___closed__0 = (const lean_object*)&l_Lean_Parser_many1Indent___closed__0_value;
static lean_once_cell_t l_Lean_Parser_many1Indent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_many1Indent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "many1Indent"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 214, 77, 50, 137, 69, 220, 172)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 342, .m_capacity = 342, .m_length = 341, .m_data = "The parser `many1Indent(p)` is equivalent to `withPosition((colGe p)+)`. This has the effect of\nparsing one or more occurrences of `p`, where each subsequent `p` parse needs to be indented\nthe same or more than the first parse.\n\nThis parser has arity 1, and returns a list of the results from `p`.\n`p` is \"auto-grouped\" if it is not arity 1."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "manyIndent"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 71, 18, 147, 220, 40, 152, 21)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 342, .m_capacity = 342, .m_length = 341, .m_data = "The parser `manyIndent(p)` is equivalent to `withPosition((colGe p)*)`. This has the effect of\nparsing zero or more occurrences of `p`, where each subsequent `p` parse needs to be indented\nthe same or more than the first parse.\n\nThis parser has arity 1, and returns a list of the results from `p`.\n`p` is \"auto-grouped\" if it is not arity 1."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_sepByIndent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_sepByIndent___closed__0;
static const lean_string_object l_Lean_Parser_sepByIndent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lean_Parser_sepByIndent___closed__1 = (const lean_object*)&l_Lean_Parser_sepByIndent___closed__1_value;
static lean_once_cell_t l_Lean_Parser_sepByIndent___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_sepByIndent___closed__2;
static lean_once_cell_t l_Lean_Parser_sepByIndent___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_sepByIndent___closed__3;
static lean_once_cell_t l_Lean_Parser_sepByIndent___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_sepByIndent___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__0_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_sepByIndent_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_sepByIndent_parenthesizer___closed__0;
static lean_once_cell_t l_Lean_Parser_sepByIndent_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_sepByIndent_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol(lean_object*);
static const lean_string_object l_Lean_Parser_patternIgnore_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* l_Lean_Parser_patternIgnore_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_patternIgnore_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* l_Lean_Parser_patternIgnore_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 215, 73, 33, 82, 129, 241, 190)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "No-op parser combinator that annotates subtrees to be ignored in syntax patterns."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppHardSpace"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 124, 7, 8, 102, 65, 59, 148)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "No-op parser that advises the pretty printer to emit a non-breaking space."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 171, 103, 94, 255, 150, 197, 120)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "No-op parser that advises the pretty printer to emit a space/soft line break."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 204, 69, 5, 170, 223, 165)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "No-op parser that advises the pretty printer to emit a hard line break."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ppRealFill"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 4, 104, 76, 91, 82, 68, 154)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "No-op parser combinator that advises the pretty printer to emit a `Format.fill` node."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppRealGroup"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 63, 239, 92, 165, 98, 92, 199)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "No-op parser combinator that advises the pretty printer to emit a `Format.group` node."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppIndent"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 194, 209, 68, 183, 68, 71, 156)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "No-op parser combinator that advises the pretty printer to indent the given syntax without grouping it."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppGroup"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 202, 60, 40, 216, 102, 169, 77)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 142, .m_capacity = 142, .m_length = 141, .m_data = "No-op parser combinator that advises the pretty printer to group and indent the given syntax.\nBy default, only syntax categories are grouped."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 177, 202, 50, 99, 27, 117, 200)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 157, .m_capacity = 157, .m_length = 156, .m_data = "No-op parser combinator that advises the pretty printer to dedent the given syntax.\nDedenting can in particular be used to counteract automatic indentation."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ppAllowUngrouped"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 185, 47, 125, 165, 106, 223, 132)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 276, .m_capacity = 276, .m_length = 275, .m_data = "No-op parser combinator that allows the pretty printer to omit the group and\nindent operation in the enclosing category parser.\n```\nsyntax ppAllowUngrouped \"by \" tacticSeq : term\n-- allows a `by` after `:=` without linebreak in between:\ntheorem foo : True := by\n  trivial\n```"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ppDedentIfGrouped"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 220, 243, 72, 104, 9, 120, 214)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 199, .m_capacity = 199, .m_length = 198, .m_data = "No-op parser combinator that advises the pretty printer to dedent the given syntax,\nif it was grouped by the category parser.\nDedenting can in particular be used to counteract automatic indentation."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ppHardLineUnlessUngrouped"};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 140, 119, 130, 113, 89, 214, 6)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 166, .m_capacity = 166, .m_length = 165, .m_data = "No-op parser combinator that prints a line break.\nThe line break is soft if the combinator is followed\nby an ungrouped parser (see ppAllowUngrouped), otherwise hard."};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_ppHardSpace_formatter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_ppHardSpace_formatter___redArg___closed__0 = (const lean_object*)&l_Lean_ppHardSpace_formatter___redArg___closed__0_value;
static const lean_ctor_object l_Lean_ppHardSpace_formatter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppHardSpace_formatter___redArg___closed__0_value)}};
static const lean_object* l_Lean_ppHardSpace_formatter___redArg___closed__1 = (const lean_object*)&l_Lean_ppHardSpace_formatter___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ppDedent_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ppDedent_formatter___closed__0;
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "termRegister_parser_alias(Kind:=_)______"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value_aux_0),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 36, 196, 99, 128, 246, 50)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "register_parser_alias "};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__4_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_antiquotNestedExpr_formatter___closed__3_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__6_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__8_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__10_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__9_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__11_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_termParser_formatter___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__12_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ") "};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__15_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__14_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__16_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_group_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__17_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__18_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__5_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__19_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_strLit_formatter___closed__1_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__21_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__24_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__20_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__25_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_ident_formatter___closed__1_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__26_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__27_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value;
static const lean_string_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__29_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__30_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__23_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__31_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__32_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__13_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_optional_formatter___closed__1_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__33_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__3_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__28_value),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__34_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value;
static const lean_ctor_object l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__35_value)}};
static const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36 = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value;
LEAN_EXPORT const lean_object* l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________ = (const lean_object*)&l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__36_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expected non-overloaded constant name"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "PrettyPrinter.Formatter.registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Formatter"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__2_value),LEAN_SCALAR_PTR_LITERAL(126, 243, 114, 121, 141, 142, 42, 100)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "PrettyPrinter.Parenthesizer.registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Parenthesizer"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 187, 150, 116, 216, 103, 117, 60)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "kind\?"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(234, 251, 71, 75, 78, 98, 206, 187)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Parser.registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "registerAlias"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(212, 182, 194, 13, 246, 198, 212, 204)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(81, 39, 139, 251, 9, 82, 71, 189)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37_value)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47_value;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58;
static const lean_string_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59_value;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60_value;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62;
static lean_once_cell_t l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__63;
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64 = (const lean_object*)&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_fill___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_group___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_patternIgnore_formatter___closed__1_value)} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 165, 69, 201, 179, 176, 38, 97)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 56, 209, 55, 154, 125, 240, 2)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 164, 225, 181, 149, 187, 81, 113)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__1_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppDedentIfGrouped_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__17_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppDedent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__22_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 142, 232, 190, 100, 212, 29, 41)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppIndent_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__26_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 219, 143, 167, 248, 5, 230, 49)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 184, 190, 137, 27, 87, 63, 174)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__4_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__6_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 180, 65, 169, 196, 28, 141, 221)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppGroup_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__39_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 168, 190, 83, 177, 86, 113, 221)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__49_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__52_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_group_formatter___closed__1_value)} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__54_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0_value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__57_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__59_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_patternIgnore_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__61_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_patternIgnore_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__63_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___redArg(lean_object* v_n_1_, lean_object* v_p_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_8_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
v___x_9_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_9_, 0, v_n_1_);
lean_closure_set(v___x_9_, 1, v_p_2_);
v___x_10_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed), 5, 0);
v___x_11_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_11_, 0, v___x_9_);
lean_closure_set(v___x_11_, 1, v___x_10_);
v___x_12_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_8_, v___x_11_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_12_;
}
}
LEAN_EXPORT void l_Lean_Parser_leadingNode_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1_ = stack[0].m_obj;
lean_object* v_p_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_res_13_;
v_res_13_ = l_Lean_Parser_leadingNode_formatter___redArg(v_n_1_, v_p_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg___boxed(lean_object* v_n_14_, lean_object* v_p_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Parser_leadingNode_formatter___redArg(v_n_14_, v_p_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
return v_res_21_;
}
}
lean_object* l_Lean_Parser_leadingNode_formatter(lean_object* v_n_22_, lean_object* v_prec_23_, lean_object* v_p_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Parser_leadingNode_formatter___redArg(v_n_22_, v_p_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lean_Parser_leadingNode_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_22_ = stack[0].m_obj;
lean_object* v_prec_23_ = stack[1].m_obj;
lean_object* v_p_24_ = stack[2].m_obj;
lean_object* v_a_25_ = stack[3].m_obj;
lean_object* v_a_26_ = stack[4].m_obj;
lean_object* v_a_27_ = stack[5].m_obj;
lean_object* v_a_28_ = stack[6].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Parser_leadingNode_formatter(v_n_22_, v_prec_23_, v_p_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object* v_n_32_, lean_object* v_prec_33_, lean_object* v_p_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Parser_leadingNode_formatter(v_n_32_, v_prec_33_, v_p_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_prec_33_);
return v_res_40_;
}
}
lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l_Lean_Parser_termParser_formatter___redArg___closed__1));
v___x_50_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_49_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_50_;
}
}
LEAN_EXPORT void l_Lean_Parser_termParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_44_ = stack[0].m_obj;
lean_object* v_a_45_ = stack[1].m_obj;
lean_object* v_a_46_ = stack[2].m_obj;
lean_object* v_a_47_ = stack[3].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_Parser_termParser_formatter___redArg(v_a_44_, v_a_45_, v_a_46_, v_a_47_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg___boxed(lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Parser_termParser_formatter___redArg(v_a_52_, v_a_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
return v_res_57_;
}
}
lean_object* l_Lean_Parser_termParser_formatter(lean_object* v_prec_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Parser_termParser_formatter___redArg(v_a_59_, v_a_60_, v_a_61_, v_a_62_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_Parser_termParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_prec_58_ = stack[0].m_obj;
lean_object* v_a_59_ = stack[1].m_obj;
lean_object* v_a_60_ = stack[2].m_obj;
lean_object* v_a_61_ = stack[3].m_obj;
lean_object* v_a_62_ = stack[4].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Parser_termParser_formatter(v_prec_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object* v_prec_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Parser_termParser_formatter(v_prec_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_prec_66_);
return v_res_72_;
}
}
lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object* v_prec_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Parser_termParser_formatter___redArg___closed__1));
v___x_80_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_79_, v_prec_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_Parser_termParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_prec_73_ = stack[0].m_obj;
lean_object* v_a_74_ = stack[1].m_obj;
lean_object* v_a_75_ = stack[2].m_obj;
lean_object* v_a_76_ = stack[3].m_obj;
lean_object* v_a_77_ = stack[4].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Parser_termParser_parenthesizer(v_prec_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object* v_prec_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Parser_termParser_parenthesizer(v_prec_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
return v_res_88_;
}
}
lean_object* l_Lean_Parser_commandParser_formatter___redArg(lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Parser_commandParser_formatter___redArg___closed__1));
v___x_98_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_97_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
return v___x_98_;
}
}
LEAN_EXPORT void l_Lean_Parser_commandParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_92_ = stack[0].m_obj;
lean_object* v_a_93_ = stack[1].m_obj;
lean_object* v_a_94_ = stack[2].m_obj;
lean_object* v_a_95_ = stack[3].m_obj;
lean_object* v_res_99_;
v_res_99_ = l_Lean_Parser_commandParser_formatter___redArg(v_a_92_, v_a_93_, v_a_94_, v_a_95_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg___boxed(lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Parser_commandParser_formatter___redArg(v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
return v_res_105_;
}
}
lean_object* l_Lean_Parser_commandParser_formatter(lean_object* v_rbp_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Parser_commandParser_formatter___redArg(v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_Parser_commandParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_106_ = stack[0].m_obj;
lean_object* v_a_107_ = stack[1].m_obj;
lean_object* v_a_108_ = stack[2].m_obj;
lean_object* v_a_109_ = stack[3].m_obj;
lean_object* v_a_110_ = stack[4].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_Parser_commandParser_formatter(v_rbp_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object* v_rbp_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Parser_commandParser_formatter(v_rbp_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_rbp_114_);
return v_res_120_;
}
}
lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object* v_rbp_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Parser_commandParser_formatter___redArg___closed__1));
v___x_128_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_127_, v_rbp_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_128_;
}
}
LEAN_EXPORT void l_Lean_Parser_commandParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_121_ = stack[0].m_obj;
lean_object* v_a_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_a_124_ = stack[3].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Lean_Parser_commandParser_parenthesizer(v_rbp_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer___boxed(lean_object* v_rbp_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Parser_commandParser_parenthesizer(v_rbp_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_136_;
}
}
lean_object* l_Lean_Parser_atomic_formatter(lean_object* v_p_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_a_139_);
lean_inc_ref(v_a_138_);
v___x_143_ = lean_apply_5(v_p_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT void l_Lean_Parser_atomic_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_137_ = stack[0].m_obj;
lean_object* v_a_138_ = stack[1].m_obj;
lean_object* v_a_139_ = stack[2].m_obj;
lean_object* v_a_140_ = stack[3].m_obj;
lean_object* v_a_141_ = stack[4].m_obj;
lean_object* v_res_144_;
v_res_144_ = l_Lean_Parser_atomic_formatter(v_p_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object* v_p_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Parser_atomic_formatter(v_p_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_151_;
}
}
lean_object* l_Lean_Parser_setExpected_formatter___redArg(lean_object* v_p_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
lean_inc(v_a_156_);
lean_inc_ref(v_a_155_);
lean_inc(v_a_154_);
lean_inc_ref(v_a_153_);
v___x_158_ = lean_apply_5(v_p_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, lean_box(0));
return v___x_158_;
}
}
LEAN_EXPORT void l_Lean_Parser_setExpected_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_152_ = stack[0].m_obj;
lean_object* v_a_153_ = stack[1].m_obj;
lean_object* v_a_154_ = stack[2].m_obj;
lean_object* v_a_155_ = stack[3].m_obj;
lean_object* v_a_156_ = stack[4].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lean_Parser_setExpected_formatter___redArg(v_p_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg___boxed(lean_object* v_p_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Parser_setExpected_formatter___redArg(v_p_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_166_;
}
}
lean_object* l_Lean_Parser_setExpected_formatter(lean_object* v_expected_167_, lean_object* v_p_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
v___x_174_ = lean_apply_5(v_p_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, lean_box(0));
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_Parser_setExpected_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_expected_167_ = stack[0].m_obj;
lean_object* v_p_168_ = stack[1].m_obj;
lean_object* v_a_169_ = stack[2].m_obj;
lean_object* v_a_170_ = stack[3].m_obj;
lean_object* v_a_171_ = stack[4].m_obj;
lean_object* v_a_172_ = stack[5].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Parser_setExpected_formatter(v_expected_167_, v_p_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object* v_expected_176_, lean_object* v_p_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Parser_setExpected_formatter(v_expected_176_, v_p_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_expected_176_);
return v_res_183_;
}
}
lean_object* l_Lean_Parser_symbol_formatter(lean_object* v_sym_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___boxed), 6, 1);
lean_closure_set(v___x_190_, 0, v_sym_184_);
v___x_191_ = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(v___x_190_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
return v___x_191_;
}
}
LEAN_EXPORT void l_Lean_Parser_symbol_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_184_ = stack[0].m_obj;
lean_object* v_a_185_ = stack[1].m_obj;
lean_object* v_a_186_ = stack[2].m_obj;
lean_object* v_a_187_ = stack[3].m_obj;
lean_object* v_a_188_ = stack[4].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_Parser_symbol_formatter(v_sym_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object* v_sym_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Parser_symbol_formatter(v_sym_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_199_;
}
}
lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg(lean_object* v_p_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
v___x_206_ = lean_apply_5(v_p_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, lean_box(0));
return v___x_206_;
}
}
LEAN_EXPORT void l_Lean_Parser_adaptCacheableContext_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_200_ = stack[0].m_obj;
lean_object* v_a_201_ = stack[1].m_obj;
lean_object* v_a_202_ = stack[2].m_obj;
lean_object* v_a_203_ = stack[3].m_obj;
lean_object* v_a_204_ = stack[4].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lean_Parser_adaptCacheableContext_formatter___redArg(v_p_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg___boxed(lean_object* v_p_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Parser_adaptCacheableContext_formatter___redArg(v_p_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_214_;
}
}
lean_object* l_Lean_Parser_adaptCacheableContext_formatter(lean_object* v_f_215_, lean_object* v_p_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_222_; 
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
v___x_222_ = lean_apply_5(v_p_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_222_;
}
}
LEAN_EXPORT void l_Lean_Parser_adaptCacheableContext_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_215_ = stack[0].m_obj;
lean_object* v_p_216_ = stack[1].m_obj;
lean_object* v_a_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_a_219_ = stack[4].m_obj;
lean_object* v_a_220_ = stack[5].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_Lean_Parser_adaptCacheableContext_formatter(v_f_215_, v_p_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___boxed(lean_object* v_f_224_, lean_object* v_p_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Parser_adaptCacheableContext_formatter(v_f_224_, v_p_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_f_224_);
return v_res_231_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(lean_object* v_p_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc(v_a_234_);
lean_inc_ref(v_a_233_);
v___x_238_ = lean_apply_5(v_p_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, lean_box(0));
return v___x_238_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_232_ = stack[0].m_obj;
lean_object* v_a_233_ = stack[1].m_obj;
lean_object* v_a_234_ = stack[2].m_obj;
lean_object* v_a_235_ = stack[3].m_obj;
lean_object* v_a_236_ = stack[4].m_obj;
lean_object* v_res_239_;
v_res_239_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(v_p_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg___boxed(lean_object* v_p_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(v_p_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_246_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(lean_object* v_i_247_, lean_object* v_p_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; 
lean_inc(v_a_252_);
lean_inc_ref(v_a_251_);
lean_inc(v_a_250_);
lean_inc_ref(v_a_249_);
v___x_254_ = lean_apply_5(v_p_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, lean_box(0));
return v___x_254_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_247_ = stack[0].m_obj;
lean_object* v_p_248_ = stack[1].m_obj;
lean_object* v_a_249_ = stack[2].m_obj;
lean_object* v_a_250_ = stack[3].m_obj;
lean_object* v_a_251_ = stack[4].m_obj;
lean_object* v_a_252_ = stack[5].m_obj;
lean_object* v_res_255_;
v_res_255_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(v_i_247_, v_p_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(lean_object* v_i_256_, lean_object* v_p_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(v_i_256_, v_p_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_i_256_);
return v_res_263_;
}
}
lean_object* l_Lean_Parser_decQuotDepth_formatter(lean_object* v_p_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_270_; 
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
v___x_270_ = lean_apply_5(v_p_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, lean_box(0));
return v___x_270_;
}
}
LEAN_EXPORT void l_Lean_Parser_decQuotDepth_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_264_ = stack[0].m_obj;
lean_object* v_a_265_ = stack[1].m_obj;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_Parser_decQuotDepth_formatter(v_p_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter___boxed(lean_object* v_p_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Parser_decQuotDepth_formatter(v_p_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_278_;
}
}
lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
v___x_301_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__8));
v___x_302_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_300_, v___x_301_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
return v___x_302_;
}
}
LEAN_EXPORT void l_Lean_Parser_antiquotNestedExpr_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_295_ = stack[0].m_obj;
lean_object* v_a_296_ = stack[1].m_obj;
lean_object* v_a_297_ = stack[2].m_obj;
lean_object* v_a_298_ = stack[3].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lean_Parser_antiquotNestedExpr_formatter(v_a_295_, v_a_296_, v_a_297_, v_a_298_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___boxed(lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Parser_antiquotNestedExpr_formatter(v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_309_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15(){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_319_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_320_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
v___x_321_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__3));
v___x_322_ = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter___boxed), 5, 0);
v___x_323_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_319_, v___x_320_, v___x_321_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_324_;
v_res_324_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___boxed(lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_formatter___closed__2(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter___boxed), 5, 0);
v___x_331_ = ((lean_object*)(l_Lean_Parser_antiquotExpr_formatter___closed__1));
v___x_332_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_332_, 0, v___x_331_);
lean_closure_set(v___x_332_, 1, v___x_330_);
return v___x_332_;
}
}
lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed), 5, 0);
v___x_339_ = lean_obj_once(&l_Lean_Parser_antiquotExpr_formatter___closed__2, &l_Lean_Parser_antiquotExpr_formatter___closed__2_once, _init_l_Lean_Parser_antiquotExpr_formatter___closed__2);
v___x_340_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_338_, v___x_339_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
return v___x_340_;
}
}
LEAN_EXPORT void l_Lean_Parser_antiquotExpr_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_333_ = stack[0].m_obj;
lean_object* v_a_334_ = stack[1].m_obj;
lean_object* v_a_335_ = stack[2].m_obj;
lean_object* v_a_336_ = stack[3].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Lean_Parser_antiquotExpr_formatter(v_a_333_, v_a_334_, v_a_335_, v_a_336_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter___boxed(lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Parser_antiquotExpr_formatter(v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(lean_object* v_sym_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(v_sym_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_354_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_348_ = stack[0].m_obj;
lean_object* v___y_349_ = stack[1].m_obj;
lean_object* v___y_350_ = stack[2].m_obj;
lean_object* v___y_351_ = stack[3].m_obj;
lean_object* v___y_352_ = stack[4].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(v_sym_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed(lean_object* v_sym_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(v_sym_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_362_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg(lean_object* v_sym_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___f_369_; lean_object* v___x_370_; 
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_369_, 0, v_sym_363_);
v___x_370_ = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(v___f_369_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_370_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_363_ = stack[0].m_obj;
lean_object* v_a_364_ = stack[1].m_obj;
lean_object* v_a_365_ = stack[2].m_obj;
lean_object* v_a_366_ = stack[3].m_obj;
lean_object* v_a_367_ = stack[4].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg(v_sym_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___boxed(lean_object* v_sym_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg(v_sym_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_378_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object* v_sym_379_, uint8_t v_includeIdent_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Parser_nonReservedSymbol_formatter___redArg(v_sym_379_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_379_ = stack[0].m_obj;
uint8_t v_includeIdent_380_ = stack[1].m_num;
lean_object* v_a_381_ = stack[2].m_obj;
lean_object* v_a_382_ = stack[3].m_obj;
lean_object* v_a_383_ = stack[4].m_obj;
lean_object* v_a_384_ = stack[5].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Parser_nonReservedSymbol_formatter(v_sym_379_, v_includeIdent_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object* v_sym_388_, lean_object* v_includeIdent_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
uint8_t v_includeIdent_boxed_395_; lean_object* v_res_396_; 
v_includeIdent_boxed_395_ = lean_unbox(v_includeIdent_389_);
v_res_396_ = l_Lean_Parser_nonReservedSymbol_formatter(v_sym_388_, v_includeIdent_boxed_395_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
return v_res_396_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0(lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_398_);
return v___x_402_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_397_ = stack[0].m_obj;
lean_object* v___y_398_ = stack[1].m_obj;
lean_object* v___y_399_ = stack[2].m_obj;
lean_object* v___y_400_ = stack[3].m_obj;
lean_object* v_res_403_;
v_res_403_ = l_Lean_Parser_mkAntiquot_formatter___lam__0(v___y_397_, v___y_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_403_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0___boxed(lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Parser_mkAntiquot_formatter___lam__0(v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1(uint8_t v_anonymous_416_, lean_object* v_name_417_, lean_object* v___f_418_, lean_object* v___f_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
if (v_anonymous_416_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v___f_419_);
v___x_425_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
v___x_426_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3));
v___x_427_ = lean_box(v_anonymous_416_);
v___x_428_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(v___x_428_, 0, v_name_417_);
lean_closure_set(v___x_428_, 1, v___x_427_);
v___x_429_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_429_, 0, v___x_426_);
lean_closure_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_430_, 0, v___f_418_);
lean_closure_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_425_, v___x_430_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_432_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
v___x_433_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__3));
v___x_434_ = 0;
v___x_435_ = lean_box(v___x_434_);
v___x_436_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(v___x_436_, 0, v_name_417_);
lean_closure_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_437_, 0, v___x_433_);
lean_closure_set(v___x_437_, 1, v___x_436_);
v___x_438_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_438_, 0, v___f_418_);
lean_closure_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_439_, 0, v___x_432_);
lean_closure_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed), 5, 0);
v___x_441_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_441_, 0, v___x_440_);
lean_closure_set(v___x_441_, 1, v___f_419_);
v___x_442_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_439_, v___x_441_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_442_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_formatter___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_anonymous_416_ = stack[0].m_num;
lean_object* v_name_417_ = stack[1].m_obj;
lean_object* v___f_418_ = stack[2].m_obj;
lean_object* v___f_419_ = stack[3].m_obj;
lean_object* v___y_420_ = stack[4].m_obj;
lean_object* v___y_421_ = stack[5].m_obj;
lean_object* v___y_422_ = stack[6].m_obj;
lean_object* v___y_423_ = stack[7].m_obj;
lean_object* v_res_443_;
v_res_443_ = l_Lean_Parser_mkAntiquot_formatter___lam__1(v_anonymous_416_, v_name_417_, v___f_418_, v___f_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(lean_object* v_anonymous_444_, lean_object* v_name_445_, lean_object* v___f_446_, lean_object* v___f_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v_anonymous_boxed_453_; lean_object* v_res_454_; 
v_anonymous_boxed_453_ = lean_unbox(v_anonymous_444_);
v_res_454_ = l_Lean_Parser_mkAntiquot_formatter___lam__1(v_anonymous_boxed_453_, v_name_445_, v___f_446_, v___f_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_454_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2(lean_object* v___x_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Parser_symbol_formatter(v___x_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_formatter___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_455_ = stack[0].m_obj;
lean_object* v___y_456_ = stack[1].m_obj;
lean_object* v___y_457_ = stack[2].m_obj;
lean_object* v___y_458_ = stack[3].m_obj;
lean_object* v___y_459_ = stack[4].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_Parser_mkAntiquot_formatter___lam__2(v___x_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2___boxed(lean_object* v___x_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Parser_mkAntiquot_formatter___lam__2(v___x_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3(lean_object* v___f_470_, lean_object* v___x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___f_470_, v___x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_477_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_formatter___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_470_ = stack[0].m_obj;
lean_object* v___x_471_ = stack[1].m_obj;
lean_object* v___y_472_ = stack[2].m_obj;
lean_object* v___y_473_ = stack[3].m_obj;
lean_object* v___y_474_ = stack[4].m_obj;
lean_object* v___y_475_ = stack[5].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_Parser_mkAntiquot_formatter___lam__3(v___f_470_, v___x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed(lean_object* v___f_479_, lean_object* v___x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Parser_mkAntiquot_formatter___lam__3(v___f_479_, v___x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object* v_name_505_, lean_object* v_kind_506_, uint8_t v_anonymous_507_, uint8_t v_isPseudoKind_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___x_516_; lean_object* v___y_517_; lean_object* v___y_519_; 
v___f_514_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
v___f_515_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__1));
v___x_516_ = lean_box(v_anonymous_507_);
v___y_517_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed), 9, 4);
lean_closure_set(v___y_517_, 0, v___x_516_);
lean_closure_set(v___y_517_, 1, v_name_505_);
lean_closure_set(v___y_517_, 2, v___f_514_);
lean_closure_set(v___y_517_, 3, v___f_515_);
if (v_isPseudoKind_508_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
v___y_519_ = v___x_531_;
goto v___jp_518_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__10));
v___y_519_ = v___x_532_;
goto v___jp_518_;
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_kind_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___f_529_; lean_object* v___x_530_; 
lean_inc(v___y_519_);
v___x_520_ = l_Lean_Name_append(v_kind_506_, v___y_519_);
v___x_521_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__3));
v_kind_522_ = l_Lean_Name_append(v___x_520_, v___x_521_);
v___f_523_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__5));
v___x_524_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__8));
v___x_525_ = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_formatter___boxed), 5, 0);
v___x_526_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_526_, 0, v___x_525_);
lean_closure_set(v___x_526_, 1, v___y_517_);
v___x_527_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_527_, 0, v___f_514_);
lean_closure_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_528_, 0, v___x_524_);
lean_closure_set(v___x_528_, 1, v___x_527_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed), 7, 2);
lean_closure_set(v___f_529_, 0, v___f_523_);
lean_closure_set(v___f_529_, 1, v___x_528_);
v___x_530_ = l_Lean_Parser_leadingNode_formatter___redArg(v_kind_522_, v___f_529_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_530_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_505_ = stack[0].m_obj;
lean_object* v_kind_506_ = stack[1].m_obj;
uint8_t v_anonymous_507_ = stack[2].m_num;
uint8_t v_isPseudoKind_508_ = stack[3].m_num;
lean_object* v_a_509_ = stack[4].m_obj;
lean_object* v_a_510_ = stack[5].m_obj;
lean_object* v_a_511_ = stack[6].m_obj;
lean_object* v_a_512_ = stack[7].m_obj;
lean_object* v_res_533_;
v_res_533_ = l_Lean_Parser_mkAntiquot_formatter(v_name_505_, v_kind_506_, v_anonymous_507_, v_isPseudoKind_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object* v_name_534_, lean_object* v_kind_535_, lean_object* v_anonymous_536_, lean_object* v_isPseudoKind_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
uint8_t v_anonymous_boxed_543_; uint8_t v_isPseudoKind_boxed_544_; lean_object* v_res_545_; 
v_anonymous_boxed_543_ = lean_unbox(v_anonymous_536_);
v_isPseudoKind_boxed_544_ = lean_unbox(v_isPseudoKind_537_);
v_res_545_ = l_Lean_Parser_mkAntiquot_formatter(v_name_534_, v_kind_535_, v_anonymous_boxed_543_, v_isPseudoKind_boxed_544_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
return v_res_545_;
}
}
lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg(lean_object* v_p_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
lean_inc(v_a_550_);
lean_inc_ref(v_a_549_);
lean_inc(v_a_548_);
lean_inc_ref(v_a_547_);
v___x_552_ = lean_apply_5(v_p_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, lean_box(0));
return v___x_552_;
}
}
LEAN_EXPORT void l_Lean_Parser_setExpected_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_546_ = stack[0].m_obj;
lean_object* v_a_547_ = stack[1].m_obj;
lean_object* v_a_548_ = stack[2].m_obj;
lean_object* v_a_549_ = stack[3].m_obj;
lean_object* v_a_550_ = stack[4].m_obj;
lean_object* v_res_553_;
v_res_553_ = l_Lean_Parser_setExpected_parenthesizer___redArg(v_p_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg___boxed(lean_object* v_p_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Parser_setExpected_parenthesizer___redArg(v_p_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_560_;
}
}
lean_object* l_Lean_Parser_setExpected_parenthesizer(lean_object* v_expected_561_, lean_object* v_p_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; 
lean_inc(v_a_566_);
lean_inc_ref(v_a_565_);
lean_inc(v_a_564_);
lean_inc_ref(v_a_563_);
v___x_568_ = lean_apply_5(v_p_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, lean_box(0));
return v___x_568_;
}
}
LEAN_EXPORT void l_Lean_Parser_setExpected_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_expected_561_ = stack[0].m_obj;
lean_object* v_p_562_ = stack[1].m_obj;
lean_object* v_a_563_ = stack[2].m_obj;
lean_object* v_a_564_ = stack[3].m_obj;
lean_object* v_a_565_ = stack[4].m_obj;
lean_object* v_a_566_ = stack[5].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_Parser_setExpected_parenthesizer(v_expected_561_, v_p_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object* v_expected_570_, lean_object* v_p_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Parser_setExpected_parenthesizer(v_expected_570_, v_p_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_expected_570_);
return v_res_577_;
}
}
lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object* v_sym_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_584_, 0, v_sym_578_);
v___x_585_ = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(v___x_584_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
return v___x_585_;
}
}
LEAN_EXPORT void l_Lean_Parser_symbol_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_578_ = stack[0].m_obj;
lean_object* v_a_579_ = stack[1].m_obj;
lean_object* v_a_580_ = stack[2].m_obj;
lean_object* v_a_581_ = stack[3].m_obj;
lean_object* v_a_582_ = stack[4].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_Parser_symbol_parenthesizer(v_sym_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object* v_sym_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Parser_symbol_parenthesizer(v_sym_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_593_;
}
}
lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(lean_object* v_p_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; 
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
lean_inc(v_a_596_);
lean_inc_ref(v_a_595_);
v___x_600_ = lean_apply_5(v_p_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, lean_box(0));
return v___x_600_;
}
}
LEAN_EXPORT void l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_594_ = stack[0].m_obj;
lean_object* v_a_595_ = stack[1].m_obj;
lean_object* v_a_596_ = stack[2].m_obj;
lean_object* v_a_597_ = stack[3].m_obj;
lean_object* v_a_598_ = stack[4].m_obj;
lean_object* v_res_601_;
v_res_601_ = l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(v_p_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg___boxed(lean_object* v_p_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(v_p_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_608_;
}
}
lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer(lean_object* v_f_609_, lean_object* v_p_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; 
lean_inc(v_a_614_);
lean_inc_ref(v_a_613_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
v___x_616_ = lean_apply_5(v_p_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, lean_box(0));
return v___x_616_;
}
}
LEAN_EXPORT void l_Lean_Parser_adaptCacheableContext_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_609_ = stack[0].m_obj;
lean_object* v_p_610_ = stack[1].m_obj;
lean_object* v_a_611_ = stack[2].m_obj;
lean_object* v_a_612_ = stack[3].m_obj;
lean_object* v_a_613_ = stack[4].m_obj;
lean_object* v_a_614_ = stack[5].m_obj;
lean_object* v_res_617_;
v_res_617_ = l_Lean_Parser_adaptCacheableContext_parenthesizer(v_f_609_, v_p_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(lean_object* v_f_618_, lean_object* v_p_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Parser_adaptCacheableContext_parenthesizer(v_f_618_, v_p_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec_ref(v_f_618_);
return v_res_625_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(lean_object* v_p_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
lean_inc(v_a_630_);
lean_inc_ref(v_a_629_);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
v___x_632_ = lean_apply_5(v_p_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, lean_box(0));
return v___x_632_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_626_ = stack[0].m_obj;
lean_object* v_a_627_ = stack[1].m_obj;
lean_object* v_a_628_ = stack[2].m_obj;
lean_object* v_a_629_ = stack[3].m_obj;
lean_object* v_a_630_ = stack[4].m_obj;
lean_object* v_res_633_;
v_res_633_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(v_p_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg___boxed(lean_object* v_p_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(v_p_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_640_;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(lean_object* v_i_641_, lean_object* v_p_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_648_; 
lean_inc(v_a_646_);
lean_inc_ref(v_a_645_);
lean_inc(v_a_644_);
lean_inc_ref(v_a_643_);
v___x_648_ = lean_apply_5(v_p_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, lean_box(0));
return v___x_648_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_641_ = stack[0].m_obj;
lean_object* v_p_642_ = stack[1].m_obj;
lean_object* v_a_643_ = stack[2].m_obj;
lean_object* v_a_644_ = stack[3].m_obj;
lean_object* v_a_645_ = stack[4].m_obj;
lean_object* v_a_646_ = stack[5].m_obj;
lean_object* v_res_649_;
v_res_649_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(v_i_641_, v_p_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
stack->m_obj
 = v_res_649_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(lean_object* v_i_650_, lean_object* v_p_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(v_i_650_, v_p_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_i_650_);
return v_res_657_;
}
}
lean_object* l_Lean_Parser_decQuotDepth_parenthesizer(lean_object* v_p_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; 
lean_inc(v_a_662_);
lean_inc_ref(v_a_661_);
lean_inc(v_a_660_);
lean_inc_ref(v_a_659_);
v___x_664_ = lean_apply_5(v_p_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, lean_box(0));
return v___x_664_;
}
}
LEAN_EXPORT void l_Lean_Parser_decQuotDepth_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_658_ = stack[0].m_obj;
lean_object* v_a_659_ = stack[1].m_obj;
lean_object* v_a_660_ = stack[2].m_obj;
lean_object* v_a_661_ = stack[3].m_obj;
lean_object* v_a_662_ = stack[4].m_obj;
lean_object* v_res_665_;
v_res_665_ = l_Lean_Parser_decQuotDepth_parenthesizer(v_p_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer___boxed(lean_object* v_p_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Parser_decQuotDepth_parenthesizer(v_p_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_672_;
}
}
lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(lean_object* v___x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Parser_termParser_parenthesizer(v___x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v___x_679_;
}
}
LEAN_EXPORT void l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_673_ = stack[0].m_obj;
lean_object* v___y_674_ = stack[1].m_obj;
lean_object* v___y_675_ = stack[2].m_obj;
lean_object* v___y_676_ = stack[3].m_obj;
lean_object* v___y_677_ = stack[4].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(v___x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0___boxed(lean_object* v___x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__0(v___x_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
v___x_706_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___closed__4));
v___x_707_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_705_, v___x_706_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_707_;
}
}
LEAN_EXPORT void l_Lean_Parser_antiquotNestedExpr_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_700_ = stack[0].m_obj;
lean_object* v_a_701_ = stack[1].m_obj;
lean_object* v_a_702_ = stack[2].m_obj;
lean_object* v_a_703_ = stack[3].m_obj;
lean_object* v_res_708_;
v_res_708_ = l_Lean_Parser_antiquotNestedExpr_parenthesizer(v_a_700_, v_a_701_, v_a_702_, v_a_703_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed(lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Parser_antiquotNestedExpr_parenthesizer(v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_714_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35(){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_723_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__2));
v___x_724_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___closed__1));
v___x_725_ = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed), 5, 0);
v___x_726_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_722_, v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_727_;
v_res_727_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35___boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___boxed), 5, 0);
v___x_733_ = ((lean_object*)(l_Lean_Parser_antiquotExpr_parenthesizer___closed__0));
v___x_734_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_734_, 0, v___x_733_);
lean_closure_set(v___x_734_, 1, v___x_732_);
return v___x_734_;
}
}
lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 5, 0);
v___x_741_ = lean_obj_once(&l_Lean_Parser_antiquotExpr_parenthesizer___closed__1, &l_Lean_Parser_antiquotExpr_parenthesizer___closed__1_once, _init_l_Lean_Parser_antiquotExpr_parenthesizer___closed__1);
v___x_742_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_740_, v___x_741_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_742_;
}
}
LEAN_EXPORT void l_Lean_Parser_antiquotExpr_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_735_ = stack[0].m_obj;
lean_object* v_a_736_ = stack[1].m_obj;
lean_object* v_a_737_ = stack[2].m_obj;
lean_object* v_a_738_ = stack[3].m_obj;
lean_object* v_res_743_;
v_res_743_ = l_Lean_Parser_antiquotExpr_parenthesizer(v_a_735_, v_a_736_, v_a_737_, v_a_738_);
stack->m_obj
 = v_res_743_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer___boxed(lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Parser_antiquotExpr_parenthesizer(v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
return v_res_749_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(lean_object* v_sym_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(v_sym_750_, v___y_752_, v___y_753_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_750_ = stack[0].m_obj;
lean_object* v___y_751_ = stack[1].m_obj;
lean_object* v___y_752_ = stack[2].m_obj;
lean_object* v___y_753_ = stack[3].m_obj;
lean_object* v___y_754_ = stack[4].m_obj;
lean_object* v_res_757_;
v_res_757_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(v_sym_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed(lean_object* v_sym_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0(v_sym_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(lean_object* v_sym_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; 
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_771_, 0, v_sym_765_);
v___x_772_ = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(v___f_771_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
return v___x_772_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_765_ = stack[0].m_obj;
lean_object* v_a_766_ = stack[1].m_obj;
lean_object* v_a_767_ = stack[2].m_obj;
lean_object* v_a_768_ = stack[3].m_obj;
lean_object* v_a_769_ = stack[4].m_obj;
lean_object* v_res_773_;
v_res_773_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(v_sym_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg___boxed(lean_object* v_sym_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(v_sym_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_780_;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object* v_sym_781_, uint8_t v_includeIdent_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(v_sym_781_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
return v___x_788_;
}
}
LEAN_EXPORT void l_Lean_Parser_nonReservedSymbol_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_781_ = stack[0].m_obj;
uint8_t v_includeIdent_782_ = stack[1].m_num;
lean_object* v_a_783_ = stack[2].m_obj;
lean_object* v_a_784_ = stack[3].m_obj;
lean_object* v_a_785_ = stack[4].m_obj;
lean_object* v_a_786_ = stack[5].m_obj;
lean_object* v_res_789_;
v_res_789_ = l_Lean_Parser_nonReservedSymbol_parenthesizer(v_sym_781_, v_includeIdent_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
stack->m_obj
 = v_res_789_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object* v_sym_790_, lean_object* v_includeIdent_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
uint8_t v_includeIdent_boxed_797_; lean_object* v_res_798_; 
v_includeIdent_boxed_797_ = lean_unbox(v_includeIdent_791_);
v_res_798_ = l_Lean_Parser_nonReservedSymbol_parenthesizer(v_sym_790_, v_includeIdent_boxed_797_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_798_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(lean_object* v___x_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Parser_symbol_parenthesizer(v___x_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_799_ = stack[0].m_obj;
lean_object* v___y_800_ = stack[1].m_obj;
lean_object* v___y_801_ = stack[2].m_obj;
lean_object* v___y_802_ = stack[3].m_obj;
lean_object* v___y_803_ = stack[4].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(v___x_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(lean_object* v___x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(v___x_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_813_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(uint8_t v_anonymous_816_, lean_object* v_name_817_, lean_object* v___x_818_, lean_object* v___f_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
if (v_anonymous_816_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v___f_819_);
v___x_825_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
v___x_826_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0));
v___x_827_ = lean_box(v_anonymous_816_);
v___x_828_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_828_, 0, v_name_817_);
lean_closure_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_829_, 0, v___x_826_);
lean_closure_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_830_, 0, v___x_818_);
lean_closure_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_825_, v___x_830_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_832_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___closed__1));
v___x_833_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___closed__0));
v___x_834_ = 0;
v___x_835_ = lean_box(v___x_834_);
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_836_, 0, v_name_817_);
lean_closure_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_837_, 0, v___x_833_);
lean_closure_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_838_, 0, v___x_818_);
lean_closure_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_839_, 0, v___x_832_);
lean_closure_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed), 5, 0);
v___x_841_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_841_, 0, v___x_840_);
lean_closure_set(v___x_841_, 1, v___f_819_);
v___x_842_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_839_, v___x_841_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_842_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_parenthesizer___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_anonymous_816_ = stack[0].m_num;
lean_object* v_name_817_ = stack[1].m_obj;
lean_object* v___x_818_ = stack[2].m_obj;
lean_object* v___f_819_ = stack[3].m_obj;
lean_object* v___y_820_ = stack[4].m_obj;
lean_object* v___y_821_ = stack[5].m_obj;
lean_object* v___y_822_ = stack[6].m_obj;
lean_object* v___y_823_ = stack[7].m_obj;
lean_object* v_res_843_;
v_res_843_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(v_anonymous_816_, v_name_817_, v___x_818_, v___f_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed(lean_object* v_anonymous_844_, lean_object* v_name_845_, lean_object* v___x_846_, lean_object* v___f_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_anonymous_boxed_853_; lean_object* v_res_854_; 
v_anonymous_boxed_853_ = lean_unbox(v_anonymous_844_);
v_res_854_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(v_anonymous_boxed_853_, v_name_845_, v___x_846_, v___f_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_854_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(lean_object* v___f_855_, lean_object* v___x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___f_855_, v___x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_862_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_parenthesizer___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_855_ = stack[0].m_obj;
lean_object* v___x_856_ = stack[1].m_obj;
lean_object* v___y_857_ = stack[2].m_obj;
lean_object* v___y_858_ = stack[3].m_obj;
lean_object* v___y_859_ = stack[4].m_obj;
lean_object* v___y_860_ = stack[5].m_obj;
lean_object* v_res_863_;
v_res_863_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(v___f_855_, v___x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(lean_object* v___f_864_, lean_object* v___x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(v___f_864_, v___x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_871_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__2));
v___x_878_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_879_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_879_, 0, v___x_878_);
lean_closure_set(v___x_879_, 1, v___x_877_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l_Lean_Parser_mkAntiquot_parenthesizer___closed__3, &l_Lean_Parser_mkAntiquot_parenthesizer___closed__3_once, _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__3);
v___x_881_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object* v_name_882_, lean_object* v_kind_883_, uint8_t v_anonymous_884_, uint8_t v_isPseudoKind_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___f_891_; lean_object* v___y_893_; 
v___f_891_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0));
if (v_isPseudoKind_885_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_box(0);
v___y_893_ = v___x_909_;
goto v___jp_892_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__10));
v___y_893_ = v___x_910_;
goto v___jp_892_;
}
v___jp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v_kind_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___y_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; 
lean_inc(v___y_893_);
v___x_894_ = l_Lean_Name_append(v_kind_883_, v___y_893_);
v___x_895_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__3));
v_kind_896_ = l_Lean_Name_append(v___x_894_, v___x_895_);
v___x_897_ = lean_unsigned_to_nat(1024u);
v___f_898_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__1));
v___x_899_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_900_ = lean_box(v_anonymous_884_);
lean_inc_ref(v___x_899_);
v___y_901_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1___boxed), 9, 4);
lean_closure_set(v___y_901_, 0, v___x_900_);
lean_closure_set(v___y_901_, 1, v_name_882_);
lean_closure_set(v___y_901_, 2, v___x_899_);
lean_closure_set(v___y_901_, 3, v___f_891_);
v___x_902_ = lean_obj_once(&l_Lean_Parser_mkAntiquot_parenthesizer___closed__4, &l_Lean_Parser_mkAntiquot_parenthesizer___closed__4_once, _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4);
v___x_903_ = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_parenthesizer___boxed), 5, 0);
v___x_904_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_904_, 0, v___x_903_);
lean_closure_set(v___x_904_, 1, v___y_901_);
v___x_905_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_905_, 0, v___x_899_);
lean_closure_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_906_, 0, v___x_902_);
lean_closure_set(v___x_906_, 1, v___x_905_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed), 7, 2);
lean_closure_set(v___f_907_, 0, v___f_898_);
lean_closure_set(v___f_907_, 1, v___x_906_);
v___x_908_ = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(v_kind_896_, v___x_897_, v___f_907_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
return v___x_908_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_882_ = stack[0].m_obj;
lean_object* v_kind_883_ = stack[1].m_obj;
uint8_t v_anonymous_884_ = stack[2].m_num;
uint8_t v_isPseudoKind_885_ = stack[3].m_num;
lean_object* v_a_886_ = stack[4].m_obj;
lean_object* v_a_887_ = stack[5].m_obj;
lean_object* v_a_888_ = stack[6].m_obj;
lean_object* v_a_889_ = stack[7].m_obj;
lean_object* v_res_911_;
v_res_911_ = l_Lean_Parser_mkAntiquot_parenthesizer(v_name_882_, v_kind_883_, v_anonymous_884_, v_isPseudoKind_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object* v_name_912_, lean_object* v_kind_913_, lean_object* v_anonymous_914_, lean_object* v_isPseudoKind_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_anonymous_boxed_921_; uint8_t v_isPseudoKind_boxed_922_; lean_object* v_res_923_; 
v_anonymous_boxed_921_ = lean_unbox(v_anonymous_914_);
v_isPseudoKind_boxed_922_ = lean_unbox(v_isPseudoKind_915_);
v_res_923_ = l_Lean_Parser_mkAntiquot_parenthesizer(v_name_912_, v_kind_913_, v_anonymous_boxed_921_, v_isPseudoKind_boxed_922_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_923_;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object* v_name_924_, lean_object* v_kind_925_, lean_object* v_p_926_, uint8_t v_anonymous_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_933_ = 0;
v___x_934_ = lean_box(v_anonymous_927_);
v___x_935_ = lean_box(v___x_933_);
lean_inc(v_kind_925_);
v___x_936_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(v___x_936_, 0, v_name_924_);
lean_closure_set(v___x_936_, 1, v_kind_925_);
lean_closure_set(v___x_936_, 2, v___x_934_);
lean_closure_set(v___x_936_, 3, v___x_935_);
v___x_937_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_937_, 0, v_kind_925_);
lean_closure_set(v___x_937_, 1, v_p_926_);
v___x_938_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_936_, v___x_937_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_938_;
}
}
LEAN_EXPORT void l_Lean_Parser_nodeWithAntiquot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_924_ = stack[0].m_obj;
lean_object* v_kind_925_ = stack[1].m_obj;
lean_object* v_p_926_ = stack[2].m_obj;
uint8_t v_anonymous_927_ = stack[3].m_num;
lean_object* v_a_928_ = stack[4].m_obj;
lean_object* v_a_929_ = stack[5].m_obj;
lean_object* v_a_930_ = stack[6].m_obj;
lean_object* v_a_931_ = stack[7].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Parser_nodeWithAntiquot_formatter(v_name_924_, v_kind_925_, v_p_926_, v_anonymous_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object* v_name_940_, lean_object* v_kind_941_, lean_object* v_p_942_, lean_object* v_anonymous_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
uint8_t v_anonymous_boxed_949_; lean_object* v_res_950_; 
v_anonymous_boxed_949_ = lean_unbox(v_anonymous_943_);
v_res_950_ = l_Lean_Parser_nodeWithAntiquot_formatter(v_name_940_, v_kind_941_, v_p_942_, v_anonymous_boxed_949_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_950_;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object* v_name_951_, lean_object* v_kind_952_, lean_object* v_p_953_, uint8_t v_anonymous_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_960_ = 0;
v___x_961_ = lean_box(v_anonymous_954_);
v___x_962_ = lean_box(v___x_960_);
lean_inc(v_kind_952_);
v___x_963_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_963_, 0, v_name_951_);
lean_closure_set(v___x_963_, 1, v_kind_952_);
lean_closure_set(v___x_963_, 2, v___x_961_);
lean_closure_set(v___x_963_, 3, v___x_962_);
v___x_964_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_964_, 0, v_kind_952_);
lean_closure_set(v___x_964_, 1, v_p_953_);
v___x_965_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_963_, v___x_964_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v___x_965_;
}
}
LEAN_EXPORT void l_Lean_Parser_nodeWithAntiquot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_951_ = stack[0].m_obj;
lean_object* v_kind_952_ = stack[1].m_obj;
lean_object* v_p_953_ = stack[2].m_obj;
uint8_t v_anonymous_954_ = stack[3].m_num;
lean_object* v_a_955_ = stack[4].m_obj;
lean_object* v_a_956_ = stack[5].m_obj;
lean_object* v_a_957_ = stack[6].m_obj;
lean_object* v_a_958_ = stack[7].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v_name_951_, v_kind_952_, v_p_953_, v_anonymous_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object* v_name_967_, lean_object* v_kind_968_, lean_object* v_p_969_, lean_object* v_anonymous_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
uint8_t v_anonymous_boxed_976_; lean_object* v_res_977_; 
v_anonymous_boxed_976_ = lean_unbox(v_anonymous_970_);
v_res_977_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v_name_967_, v_kind_968_, v_p_969_, v_anonymous_boxed_976_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
return v_res_977_;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object* v_kind_990_, lean_object* v_p_991_, lean_object* v_suffix_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v_kind_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
v___f_998_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
v___x_999_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__1));
v_kind_1000_ = l_Lean_Name_append(v_kind_990_, v___x_999_);
v___f_1001_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__5));
v___x_1002_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__8));
v___x_1003_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__3));
v___x_1004_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
v___x_1005_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_1005_, 0, v___x_1004_);
lean_closure_set(v___x_1005_, 1, v_p_991_);
v___x_1006_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__7));
v___x_1007_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1007_, 0, v___x_1006_);
lean_closure_set(v___x_1007_, 1, v_suffix_992_);
v___x_1008_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1008_, 0, v___x_1005_);
lean_closure_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1009_, 0, v___x_1003_);
lean_closure_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1010_, 0, v___f_998_);
lean_closure_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1011_, 0, v___x_1002_);
lean_closure_set(v___x_1011_, 1, v___x_1010_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1012_, 0, v___f_1001_);
lean_closure_set(v___f_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_Parser_leadingNode_formatter___redArg(v_kind_1000_, v___f_1012_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
return v___x_1013_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquotSplice_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_990_ = stack[0].m_obj;
lean_object* v_p_991_ = stack[1].m_obj;
lean_object* v_suffix_992_ = stack[2].m_obj;
lean_object* v_a_993_ = stack[3].m_obj;
lean_object* v_a_994_ = stack[4].m_obj;
lean_object* v_a_995_ = stack[5].m_obj;
lean_object* v_a_996_ = stack[6].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l_Lean_Parser_mkAntiquotSplice_formatter(v_kind_990_, v_p_991_, v_suffix_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter___boxed(lean_object* v_kind_1015_, lean_object* v_p_1016_, lean_object* v_suffix_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Parser_mkAntiquotSplice_formatter(v_kind_1015_, v_p_1016_, v_suffix_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1023_;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(lean_object* v_p_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_apply_5(v_p_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, lean_box(0));
return v___x_1030_;
}
}
LEAN_EXPORT void l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1024_ = stack[0].m_obj;
lean_object* v___y_1025_ = stack[1].m_obj;
lean_object* v___y_1026_ = stack[2].m_obj;
lean_object* v___y_1027_ = stack[3].m_obj;
lean_object* v___y_1028_ = stack[4].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(v_p_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed(lean_object* v_p_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(v_p_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v_res_1038_;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object* v_kind_1039_, lean_object* v_p_1040_, lean_object* v_suffix_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_inc_ref(v_p_1040_);
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1047_, 0, v_p_1040_);
lean_inc_ref(v_suffix_1041_);
lean_inc(v_kind_1039_);
v___x_1048_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_formatter___boxed), 8, 3);
lean_closure_set(v___x_1048_, 0, v_kind_1039_);
lean_closure_set(v___x_1048_, 1, v___f_1047_);
lean_closure_set(v___x_1048_, 2, v_suffix_1041_);
v___x_1049_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed), 8, 3);
lean_closure_set(v___x_1049_, 0, v_kind_1039_);
lean_closure_set(v___x_1049_, 1, v_p_1040_);
lean_closure_set(v___x_1049_, 2, v_suffix_1041_);
v___x_1050_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1048_, v___x_1049_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v___x_1050_;
}
}
LEAN_EXPORT void l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_1039_ = stack[0].m_obj;
lean_object* v_p_1040_ = stack[1].m_obj;
lean_object* v_suffix_1041_ = stack[2].m_obj;
lean_object* v_a_1042_ = stack[3].m_obj;
lean_object* v_a_1043_ = stack[4].m_obj;
lean_object* v_a_1044_ = stack[5].m_obj;
lean_object* v_a_1045_ = stack[6].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(v_kind_1039_, v_p_1040_, v_suffix_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed(lean_object* v_kind_1052_, lean_object* v_p_1053_, lean_object* v_suffix_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(v_kind_1052_, v_p_1053_, v_suffix_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1060_;
}
}
lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object* v_p_1065_, lean_object* v_sep_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_str_1076_; lean_object* v_startInclusive_1077_; lean_object* v_endExclusive_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_string_utf8_byte_size(v_sep_1066_);
v___x_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1074_, 0, v_sep_1066_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = l_String_Slice_trimAscii(v___x_1074_);
v_str_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_str_1076_);
v_startInclusive_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_startInclusive_1077_);
v_endExclusive_1078_ = lean_ctor_get(v___x_1075_, 2);
lean_inc(v_endExclusive_1078_);
lean_dec_ref(v___x_1075_);
v___x_1079_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
v___x_1080_ = lean_string_utf8_extract_fast(v_str_1076_, v_startInclusive_1077_, v_endExclusive_1078_);
lean_dec(v_endExclusive_1078_);
lean_dec(v_startInclusive_1077_);
lean_dec_ref(v_str_1076_);
v___x_1081_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__2));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
v___x_1083_ = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter___boxed), 6, 1);
lean_closure_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(v___x_1079_, v_p_1065_, v___x_1083_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
return v___x_1084_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepByElemParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1065_ = stack[0].m_obj;
lean_object* v_sep_1066_ = stack[1].m_obj;
lean_object* v_a_1067_ = stack[2].m_obj;
lean_object* v_a_1068_ = stack[3].m_obj;
lean_object* v_a_1069_ = stack[4].m_obj;
lean_object* v_a_1070_ = stack[5].m_obj;
lean_object* v_res_1085_;
v_res_1085_ = l_Lean_Parser_sepByElemParser_formatter(v_p_1065_, v_sep_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
stack->m_obj
 = v_res_1085_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object* v_p_1086_, lean_object* v_sep_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Parser_sepByElemParser_formatter(v_p_1086_, v_sep_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1093_;
}
}
lean_object* l_Lean_Parser_sepBy_formatter___redArg(lean_object* v_p_1094_, lean_object* v_sep_1095_, lean_object* v_psep_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(v___x_1102_, 0, v_p_1094_);
lean_closure_set(v___x_1102_, 1, v_sep_1095_);
v___x_1103_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1102_, v_psep_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1094_ = stack[0].m_obj;
lean_object* v_sep_1095_ = stack[1].m_obj;
lean_object* v_psep_1096_ = stack[2].m_obj;
lean_object* v_a_1097_ = stack[3].m_obj;
lean_object* v_a_1098_ = stack[4].m_obj;
lean_object* v_a_1099_ = stack[5].m_obj;
lean_object* v_a_1100_ = stack[6].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_Parser_sepBy_formatter___redArg(v_p_1094_, v_sep_1095_, v_psep_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg___boxed(lean_object* v_p_1105_, lean_object* v_sep_1106_, lean_object* v_psep_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Parser_sepBy_formatter___redArg(v_p_1105_, v_sep_1106_, v_psep_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1113_;
}
}
lean_object* l_Lean_Parser_sepBy_formatter(lean_object* v_p_1114_, lean_object* v_sep_1115_, lean_object* v_psep_1116_, uint8_t v_allowTrailingSep_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Parser_sepBy_formatter___redArg(v_p_1114_, v_sep_1115_, v_psep_1116_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1114_ = stack[0].m_obj;
lean_object* v_sep_1115_ = stack[1].m_obj;
lean_object* v_psep_1116_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_1117_ = stack[3].m_num;
lean_object* v_a_1118_ = stack[4].m_obj;
lean_object* v_a_1119_ = stack[5].m_obj;
lean_object* v_a_1120_ = stack[6].m_obj;
lean_object* v_a_1121_ = stack[7].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Parser_sepBy_formatter(v_p_1114_, v_sep_1115_, v_psep_1116_, v_allowTrailingSep_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object* v_p_1125_, lean_object* v_sep_1126_, lean_object* v_psep_1127_, lean_object* v_allowTrailingSep_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1134_; lean_object* v_res_1135_; 
v_allowTrailingSep_boxed_1134_ = lean_unbox(v_allowTrailingSep_1128_);
v_res_1135_ = l_Lean_Parser_sepBy_formatter(v_p_1125_, v_sep_1126_, v_psep_1127_, v_allowTrailingSep_boxed_1134_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1135_;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object* v_kind_1140_, lean_object* v_p_1141_, lean_object* v_suffix_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v_kind_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___x_1148_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__1));
v_kind_1149_ = l_Lean_Name_append(v_kind_1140_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(1024u);
v___f_1151_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__1));
v___x_1152_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_1153_ = lean_obj_once(&l_Lean_Parser_mkAntiquot_parenthesizer___closed__4, &l_Lean_Parser_mkAntiquot_parenthesizer___closed__4_once, _init_l_Lean_Parser_mkAntiquot_parenthesizer___closed__4);
v___x_1154_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__0));
v___x_1155_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
v___x_1156_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1156_, 0, v___x_1155_);
lean_closure_set(v___x_1156_, 1, v_p_1141_);
v___x_1157_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___closed__1));
v___x_1158_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1158_, 0, v___x_1157_);
lean_closure_set(v___x_1158_, 1, v_suffix_1142_);
v___x_1159_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1159_, 0, v___x_1156_);
lean_closure_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1160_, 0, v___x_1154_);
lean_closure_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1161_, 0, v___x_1152_);
lean_closure_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1162_, 0, v___x_1153_);
lean_closure_set(v___x_1162_, 1, v___x_1161_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed), 7, 2);
lean_closure_set(v___f_1163_, 0, v___f_1151_);
lean_closure_set(v___f_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(v_kind_1149_, v___x_1150_, v___f_1163_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
return v___x_1164_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkAntiquotSplice_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_1140_ = stack[0].m_obj;
lean_object* v_p_1141_ = stack[1].m_obj;
lean_object* v_suffix_1142_ = stack[2].m_obj;
lean_object* v_a_1143_ = stack[3].m_obj;
lean_object* v_a_1144_ = stack[4].m_obj;
lean_object* v_a_1145_ = stack[5].m_obj;
lean_object* v_a_1146_ = stack[6].m_obj;
lean_object* v_res_1165_;
v_res_1165_ = l_Lean_Parser_mkAntiquotSplice_parenthesizer(v_kind_1140_, v_p_1141_, v_suffix_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
stack->m_obj
 = v_res_1165_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed(lean_object* v_kind_1166_, lean_object* v_p_1167_, lean_object* v_suffix_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Parser_mkAntiquotSplice_parenthesizer(v_kind_1166_, v_p_1167_, v_suffix_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
return v_res_1174_;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(lean_object* v_p_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_apply_5(v_p_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, lean_box(0));
return v___x_1181_;
}
}
LEAN_EXPORT void l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1175_ = stack[0].m_obj;
lean_object* v___y_1176_ = stack[1].m_obj;
lean_object* v___y_1177_ = stack[2].m_obj;
lean_object* v___y_1178_ = stack[3].m_obj;
lean_object* v___y_1179_ = stack[4].m_obj;
lean_object* v_res_1182_;
v_res_1182_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(v_p_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
stack->m_obj
 = v_res_1182_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed(lean_object* v_p_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(v_p_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v_res_1189_;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object* v_kind_1190_, lean_object* v_p_1191_, lean_object* v_suffix_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_inc_ref(v_p_1191_);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1198_, 0, v_p_1191_);
lean_inc_ref(v_suffix_1192_);
lean_inc(v_kind_1190_);
v___x_1199_ = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1199_, 0, v_kind_1190_);
lean_closure_set(v___x_1199_, 1, v___f_1198_);
lean_closure_set(v___x_1199_, 2, v_suffix_1192_);
v___x_1200_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1200_, 0, v_kind_1190_);
lean_closure_set(v___x_1200_, 1, v_p_1191_);
lean_closure_set(v___x_1200_, 2, v_suffix_1192_);
v___x_1201_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1199_, v___x_1200_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1201_;
}
}
LEAN_EXPORT void l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_1190_ = stack[0].m_obj;
lean_object* v_p_1191_ = stack[1].m_obj;
lean_object* v_suffix_1192_ = stack[2].m_obj;
lean_object* v_a_1193_ = stack[3].m_obj;
lean_object* v_a_1194_ = stack[4].m_obj;
lean_object* v_a_1195_ = stack[5].m_obj;
lean_object* v_a_1196_ = stack[6].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(v_kind_1190_, v_p_1191_, v_suffix_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed(lean_object* v_kind_1203_, lean_object* v_p_1204_, lean_object* v_suffix_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(v_kind_1203_, v_p_1204_, v_suffix_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
return v_res_1211_;
}
}
lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object* v_p_1212_, lean_object* v_sep_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_str_1223_; lean_object* v_startInclusive_1224_; lean_object* v_endExclusive_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_string_utf8_byte_size(v_sep_1213_);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v_sep_1213_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
v___x_1222_ = l_String_Slice_trimAscii(v___x_1221_);
v_str_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_str_1223_);
v_startInclusive_1224_ = lean_ctor_get(v___x_1222_, 1);
lean_inc(v_startInclusive_1224_);
v_endExclusive_1225_ = lean_ctor_get(v___x_1222_, 2);
lean_inc(v_endExclusive_1225_);
lean_dec_ref(v___x_1222_);
v___x_1226_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
v___x_1227_ = lean_string_utf8_extract_fast(v_str_1223_, v_startInclusive_1224_, v_endExclusive_1225_);
lean_dec(v_endExclusive_1225_);
lean_dec(v_startInclusive_1224_);
lean_dec_ref(v_str_1223_);
v___x_1228_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__2));
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
v___x_1230_ = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1230_, 0, v___x_1229_);
v___x_1231_ = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(v___x_1226_, v_p_1212_, v___x_1230_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
return v___x_1231_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepByElemParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1212_ = stack[0].m_obj;
lean_object* v_sep_1213_ = stack[1].m_obj;
lean_object* v_a_1214_ = stack[2].m_obj;
lean_object* v_a_1215_ = stack[3].m_obj;
lean_object* v_a_1216_ = stack[4].m_obj;
lean_object* v_a_1217_ = stack[5].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l_Lean_Parser_sepByElemParser_parenthesizer(v_p_1212_, v_sep_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object* v_p_1233_, lean_object* v_sep_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Parser_sepByElemParser_parenthesizer(v_p_1233_, v_sep_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1240_;
}
}
lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg(lean_object* v_p_1241_, lean_object* v_sep_1242_, lean_object* v_psep_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1249_, 0, v_p_1241_);
lean_closure_set(v___x_1249_, 1, v_sep_1242_);
v___x_1250_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1249_, v_psep_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v___x_1250_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1241_ = stack[0].m_obj;
lean_object* v_sep_1242_ = stack[1].m_obj;
lean_object* v_psep_1243_ = stack[2].m_obj;
lean_object* v_a_1244_ = stack[3].m_obj;
lean_object* v_a_1245_ = stack[4].m_obj;
lean_object* v_a_1246_ = stack[5].m_obj;
lean_object* v_a_1247_ = stack[6].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l_Lean_Parser_sepBy_parenthesizer___redArg(v_p_1241_, v_sep_1242_, v_psep_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg___boxed(lean_object* v_p_1252_, lean_object* v_sep_1253_, lean_object* v_psep_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Parser_sepBy_parenthesizer___redArg(v_p_1252_, v_sep_1253_, v_psep_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1260_;
}
}
lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object* v_p_1261_, lean_object* v_sep_1262_, lean_object* v_psep_1263_, uint8_t v_allowTrailingSep_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Parser_sepBy_parenthesizer___redArg(v_p_1261_, v_sep_1262_, v_psep_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1261_ = stack[0].m_obj;
lean_object* v_sep_1262_ = stack[1].m_obj;
lean_object* v_psep_1263_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_1264_ = stack[3].m_num;
lean_object* v_a_1265_ = stack[4].m_obj;
lean_object* v_a_1266_ = stack[5].m_obj;
lean_object* v_a_1267_ = stack[6].m_obj;
lean_object* v_a_1268_ = stack[7].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_Parser_sepBy_parenthesizer(v_p_1261_, v_sep_1262_, v_psep_1263_, v_allowTrailingSep_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object* v_p_1272_, lean_object* v_sep_1273_, lean_object* v_psep_1274_, lean_object* v_allowTrailingSep_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1281_; lean_object* v_res_1282_; 
v_allowTrailingSep_boxed_1281_ = lean_unbox(v_allowTrailingSep_1275_);
v_res_1282_ = l_Lean_Parser_sepBy_parenthesizer(v_p_1272_, v_sep_1273_, v_psep_1274_, v_allowTrailingSep_boxed_1281_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
return v_res_1282_;
}
}
lean_object* l_Lean_Parser_sepBy1_formatter___redArg(lean_object* v_p_1283_, lean_object* v_sep_1284_, lean_object* v_psep_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(v___x_1291_, 0, v_p_1283_);
lean_closure_set(v___x_1291_, 1, v_sep_1284_);
v___x_1292_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(v___x_1291_, v_psep_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1283_ = stack[0].m_obj;
lean_object* v_sep_1284_ = stack[1].m_obj;
lean_object* v_psep_1285_ = stack[2].m_obj;
lean_object* v_a_1286_ = stack[3].m_obj;
lean_object* v_a_1287_ = stack[4].m_obj;
lean_object* v_a_1288_ = stack[5].m_obj;
lean_object* v_a_1289_ = stack[6].m_obj;
lean_object* v_res_1293_;
v_res_1293_ = l_Lean_Parser_sepBy1_formatter___redArg(v_p_1283_, v_sep_1284_, v_psep_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
stack->m_obj
 = v_res_1293_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg___boxed(lean_object* v_p_1294_, lean_object* v_sep_1295_, lean_object* v_psep_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Parser_sepBy1_formatter___redArg(v_p_1294_, v_sep_1295_, v_psep_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1302_;
}
}
lean_object* l_Lean_Parser_sepBy1_formatter(lean_object* v_p_1303_, lean_object* v_sep_1304_, lean_object* v_psep_1305_, uint8_t v_allowTrailingSep_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Parser_sepBy1_formatter___redArg(v_p_1303_, v_sep_1304_, v_psep_1305_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1303_ = stack[0].m_obj;
lean_object* v_sep_1304_ = stack[1].m_obj;
lean_object* v_psep_1305_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_1306_ = stack[3].m_num;
lean_object* v_a_1307_ = stack[4].m_obj;
lean_object* v_a_1308_ = stack[5].m_obj;
lean_object* v_a_1309_ = stack[6].m_obj;
lean_object* v_a_1310_ = stack[7].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l_Lean_Parser_sepBy1_formatter(v_p_1303_, v_sep_1304_, v_psep_1305_, v_allowTrailingSep_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object* v_p_1314_, lean_object* v_sep_1315_, lean_object* v_psep_1316_, lean_object* v_allowTrailingSep_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1323_; lean_object* v_res_1324_; 
v_allowTrailingSep_boxed_1323_ = lean_unbox(v_allowTrailingSep_1317_);
v_res_1324_ = l_Lean_Parser_sepBy1_formatter(v_p_1314_, v_sep_1315_, v_psep_1316_, v_allowTrailingSep_boxed_1323_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1324_;
}
}
lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg(lean_object* v_p_1325_, lean_object* v_sep_1326_, lean_object* v_psep_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1333_, 0, v_p_1325_);
lean_closure_set(v___x_1333_, 1, v_sep_1326_);
v___x_1334_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(v___x_1333_, v_psep_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
return v___x_1334_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1325_ = stack[0].m_obj;
lean_object* v_sep_1326_ = stack[1].m_obj;
lean_object* v_psep_1327_ = stack[2].m_obj;
lean_object* v_a_1328_ = stack[3].m_obj;
lean_object* v_a_1329_ = stack[4].m_obj;
lean_object* v_a_1330_ = stack[5].m_obj;
lean_object* v_a_1331_ = stack[6].m_obj;
lean_object* v_res_1335_;
v_res_1335_ = l_Lean_Parser_sepBy1_parenthesizer___redArg(v_p_1325_, v_sep_1326_, v_psep_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
stack->m_obj
 = v_res_1335_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg___boxed(lean_object* v_p_1336_, lean_object* v_sep_1337_, lean_object* v_psep_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Parser_sepBy1_parenthesizer___redArg(v_p_1336_, v_sep_1337_, v_psep_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
return v_res_1344_;
}
}
lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object* v_p_1345_, lean_object* v_sep_1346_, lean_object* v_psep_1347_, uint8_t v_allowTrailingSep_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Parser_sepBy1_parenthesizer___redArg(v_p_1345_, v_sep_1346_, v_psep_1347_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1345_ = stack[0].m_obj;
lean_object* v_sep_1346_ = stack[1].m_obj;
lean_object* v_psep_1347_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_1348_ = stack[3].m_num;
lean_object* v_a_1349_ = stack[4].m_obj;
lean_object* v_a_1350_ = stack[5].m_obj;
lean_object* v_a_1351_ = stack[6].m_obj;
lean_object* v_a_1352_ = stack[7].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_Parser_sepBy1_parenthesizer(v_p_1345_, v_sep_1346_, v_psep_1347_, v_allowTrailingSep_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object* v_p_1356_, lean_object* v_sep_1357_, lean_object* v_psep_1358_, lean_object* v_allowTrailingSep_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1365_; lean_object* v_res_1366_; 
v_allowTrailingSep_boxed_1365_ = lean_unbox(v_allowTrailingSep_1359_);
v_res_1366_ = l_Lean_Parser_sepBy1_parenthesizer(v_p_1356_, v_sep_1357_, v_psep_1358_, v_allowTrailingSep_boxed_1365_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
return v_res_1366_;
}
}
lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object* v_sym_1367_, lean_object* v_asciiSym_1368_, uint8_t v_preserveForPP_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_box(v_preserveForPP_1369_);
v___x_1376_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___boxed), 8, 3);
lean_closure_set(v___x_1376_, 0, v_sym_1367_);
lean_closure_set(v___x_1376_, 1, v_asciiSym_1368_);
lean_closure_set(v___x_1376_, 2, v___x_1375_);
v___x_1377_ = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(v___x_1376_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT void l_Lean_Parser_unicodeSymbol_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_1367_ = stack[0].m_obj;
lean_object* v_asciiSym_1368_ = stack[1].m_obj;
uint8_t v_preserveForPP_1369_ = stack[2].m_num;
lean_object* v_a_1370_ = stack[3].m_obj;
lean_object* v_a_1371_ = stack[4].m_obj;
lean_object* v_a_1372_ = stack[5].m_obj;
lean_object* v_a_1373_ = stack[6].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_Lean_Parser_unicodeSymbol_formatter(v_sym_1367_, v_asciiSym_1368_, v_preserveForPP_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter___boxed(lean_object* v_sym_1379_, lean_object* v_asciiSym_1380_, lean_object* v_preserveForPP_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
uint8_t v_preserveForPP_boxed_1387_; lean_object* v_res_1388_; 
v_preserveForPP_boxed_1387_ = lean_unbox(v_preserveForPP_1381_);
v_res_1388_ = l_Lean_Parser_unicodeSymbol_formatter(v_sym_1379_, v_asciiSym_1380_, v_preserveForPP_boxed_1387_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1388_;
}
}
lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object* v_sym_1389_, lean_object* v_asciiSym_1390_, uint8_t v_preserveForPP_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_box(v_preserveForPP_1391_);
v___x_1398_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1398_, 0, v_sym_1389_);
lean_closure_set(v___x_1398_, 1, v_asciiSym_1390_);
lean_closure_set(v___x_1398_, 2, v___x_1397_);
v___x_1399_ = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(v___x_1398_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1399_;
}
}
LEAN_EXPORT void l_Lean_Parser_unicodeSymbol_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_1389_ = stack[0].m_obj;
lean_object* v_asciiSym_1390_ = stack[1].m_obj;
uint8_t v_preserveForPP_1391_ = stack[2].m_num;
lean_object* v_a_1392_ = stack[3].m_obj;
lean_object* v_a_1393_ = stack[4].m_obj;
lean_object* v_a_1394_ = stack[5].m_obj;
lean_object* v_a_1395_ = stack[6].m_obj;
lean_object* v_res_1400_;
v_res_1400_ = l_Lean_Parser_unicodeSymbol_parenthesizer(v_sym_1389_, v_asciiSym_1390_, v_preserveForPP_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
stack->m_obj
 = v_res_1400_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object* v_sym_1401_, lean_object* v_asciiSym_1402_, lean_object* v_preserveForPP_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v_preserveForPP_boxed_1409_; lean_object* v_res_1410_; 
v_preserveForPP_boxed_1409_ = lean_unbox(v_preserveForPP_1403_);
v_res_1410_ = l_Lean_Parser_unicodeSymbol_parenthesizer(v_sym_1401_, v_asciiSym_1402_, v_preserveForPP_boxed_1409_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1410_;
}
}
lean_object* l_Lean_Parser_withCache_formatter___redArg(lean_object* v_p_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; 
lean_inc(v_a_1415_);
lean_inc_ref(v_a_1414_);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
v___x_1417_ = lean_apply_5(v_p_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, lean_box(0));
return v___x_1417_;
}
}
LEAN_EXPORT void l_Lean_Parser_withCache_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1411_ = stack[0].m_obj;
lean_object* v_a_1412_ = stack[1].m_obj;
lean_object* v_a_1413_ = stack[2].m_obj;
lean_object* v_a_1414_ = stack[3].m_obj;
lean_object* v_a_1415_ = stack[4].m_obj;
lean_object* v_res_1418_;
v_res_1418_ = l_Lean_Parser_withCache_formatter___redArg(v_p_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
stack->m_obj
 = v_res_1418_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg___boxed(lean_object* v_p_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Parser_withCache_formatter___redArg(v_p_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
lean_object* l_Lean_Parser_withCache_formatter(lean_object* v_parserName_1426_, lean_object* v_p_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; 
lean_inc(v_a_1431_);
lean_inc_ref(v_a_1430_);
lean_inc(v_a_1429_);
lean_inc_ref(v_a_1428_);
v___x_1433_ = lean_apply_5(v_p_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, lean_box(0));
return v___x_1433_;
}
}
LEAN_EXPORT void l_Lean_Parser_withCache_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_parserName_1426_ = stack[0].m_obj;
lean_object* v_p_1427_ = stack[1].m_obj;
lean_object* v_a_1428_ = stack[2].m_obj;
lean_object* v_a_1429_ = stack[3].m_obj;
lean_object* v_a_1430_ = stack[4].m_obj;
lean_object* v_a_1431_ = stack[5].m_obj;
lean_object* v_res_1434_;
v_res_1434_ = l_Lean_Parser_withCache_formatter(v_parserName_1426_, v_p_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object* v_parserName_1435_, lean_object* v_p_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Parser_withCache_formatter(v_parserName_1435_, v_p_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_parserName_1435_);
return v_res_1442_;
}
}
lean_object* l_Lean_Parser_withCache_parenthesizer___redArg(lean_object* v_p_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; 
lean_inc(v_a_1447_);
lean_inc_ref(v_a_1446_);
lean_inc(v_a_1445_);
lean_inc_ref(v_a_1444_);
v___x_1449_ = lean_apply_5(v_p_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, lean_box(0));
return v___x_1449_;
}
}
LEAN_EXPORT void l_Lean_Parser_withCache_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1443_ = stack[0].m_obj;
lean_object* v_a_1444_ = stack[1].m_obj;
lean_object* v_a_1445_ = stack[2].m_obj;
lean_object* v_a_1446_ = stack[3].m_obj;
lean_object* v_a_1447_ = stack[4].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Lean_Parser_withCache_parenthesizer___redArg(v_p_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg___boxed(lean_object* v_p_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Parser_withCache_parenthesizer___redArg(v_p_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
return v_res_1457_;
}
}
lean_object* l_Lean_Parser_withCache_parenthesizer(lean_object* v_parserName_1458_, lean_object* v_p_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
lean_inc(v_a_1463_);
lean_inc_ref(v_a_1462_);
lean_inc(v_a_1461_);
lean_inc_ref(v_a_1460_);
v___x_1465_ = lean_apply_5(v_p_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, lean_box(0));
return v___x_1465_;
}
}
LEAN_EXPORT void l_Lean_Parser_withCache_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_parserName_1458_ = stack[0].m_obj;
lean_object* v_p_1459_ = stack[1].m_obj;
lean_object* v_a_1460_ = stack[2].m_obj;
lean_object* v_a_1461_ = stack[3].m_obj;
lean_object* v_a_1462_ = stack[4].m_obj;
lean_object* v_a_1463_ = stack[5].m_obj;
lean_object* v_res_1466_;
v_res_1466_ = l_Lean_Parser_withCache_parenthesizer(v_parserName_1458_, v_p_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
stack->m_obj
 = v_res_1466_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object* v_parserName_1467_, lean_object* v_p_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Parser_withCache_parenthesizer(v_parserName_1467_, v_p_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_parserName_1467_);
return v_res_1474_;
}
}
lean_object* l_Lean_Parser_withResetCache_formatter(lean_object* v_p_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1481_; 
lean_inc(v_a_1479_);
lean_inc_ref(v_a_1478_);
lean_inc(v_a_1477_);
lean_inc_ref(v_a_1476_);
v___x_1481_ = lean_apply_5(v_p_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, lean_box(0));
return v___x_1481_;
}
}
LEAN_EXPORT void l_Lean_Parser_withResetCache_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1475_ = stack[0].m_obj;
lean_object* v_a_1476_ = stack[1].m_obj;
lean_object* v_a_1477_ = stack[2].m_obj;
lean_object* v_a_1478_ = stack[3].m_obj;
lean_object* v_a_1479_ = stack[4].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_Lean_Parser_withResetCache_formatter(v_p_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter___boxed(lean_object* v_p_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Parser_withResetCache_formatter(v_p_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
return v_res_1489_;
}
}
lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object* v_p_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1496_; 
lean_inc(v_a_1494_);
lean_inc_ref(v_a_1493_);
lean_inc(v_a_1492_);
lean_inc_ref(v_a_1491_);
v___x_1496_ = lean_apply_5(v_p_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, lean_box(0));
return v___x_1496_;
}
}
LEAN_EXPORT void l_Lean_Parser_withResetCache_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1490_ = stack[0].m_obj;
lean_object* v_a_1491_ = stack[1].m_obj;
lean_object* v_a_1492_ = stack[2].m_obj;
lean_object* v_a_1493_ = stack[3].m_obj;
lean_object* v_a_1494_ = stack[4].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l_Lean_Parser_withResetCache_parenthesizer(v_p_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer___boxed(lean_object* v_p_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Parser_withResetCache_parenthesizer(v_p_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1504_;
}
}
lean_object* l_Lean_Parser_withPosition_formatter(lean_object* v_p_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1511_; 
lean_inc(v_a_1509_);
lean_inc_ref(v_a_1508_);
lean_inc(v_a_1507_);
lean_inc_ref(v_a_1506_);
v___x_1511_ = lean_apply_5(v_p_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, lean_box(0));
return v___x_1511_;
}
}
LEAN_EXPORT void l_Lean_Parser_withPosition_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1505_ = stack[0].m_obj;
lean_object* v_a_1506_ = stack[1].m_obj;
lean_object* v_a_1507_ = stack[2].m_obj;
lean_object* v_a_1508_ = stack[3].m_obj;
lean_object* v_a_1509_ = stack[4].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = l_Lean_Parser_withPosition_formatter(v_p_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object* v_p_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Parser_withPosition_formatter(v_p_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1519_;
}
}
lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter(lean_object* v_p_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1526_; 
lean_inc(v_a_1524_);
lean_inc_ref(v_a_1523_);
lean_inc(v_a_1522_);
lean_inc_ref(v_a_1521_);
v___x_1526_ = lean_apply_5(v_p_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, lean_box(0));
return v___x_1526_;
}
}
LEAN_EXPORT void l_Lean_Parser_withPositionAfterLinebreak_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1520_ = stack[0].m_obj;
lean_object* v_a_1521_ = stack[1].m_obj;
lean_object* v_a_1522_ = stack[2].m_obj;
lean_object* v_a_1523_ = stack[3].m_obj;
lean_object* v_a_1524_ = stack[4].m_obj;
lean_object* v_res_1527_;
v_res_1527_ = l_Lean_Parser_withPositionAfterLinebreak_formatter(v_p_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
stack->m_obj
 = v_res_1527_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter___boxed(lean_object* v_p_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Parser_withPositionAfterLinebreak_formatter(v_p_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
return v_res_1534_;
}
}
lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object* v_p_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; 
lean_inc(v_a_1539_);
lean_inc_ref(v_a_1538_);
lean_inc(v_a_1537_);
lean_inc_ref(v_a_1536_);
v___x_1541_ = lean_apply_5(v_p_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, lean_box(0));
return v___x_1541_;
}
}
LEAN_EXPORT void l_Lean_Parser_withoutPosition_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1535_ = stack[0].m_obj;
lean_object* v_a_1536_ = stack[1].m_obj;
lean_object* v_a_1537_ = stack[2].m_obj;
lean_object* v_a_1538_ = stack[3].m_obj;
lean_object* v_a_1539_ = stack[4].m_obj;
lean_object* v_res_1542_;
v_res_1542_ = l_Lean_Parser_withoutPosition_formatter(v_p_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
stack->m_obj
 = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object* v_p_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Parser_withoutPosition_formatter(v_p_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
return v_res_1549_;
}
}
lean_object* l_Lean_Parser_withoutPosition_parenthesizer(lean_object* v_p_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; 
lean_inc(v_a_1554_);
lean_inc_ref(v_a_1553_);
lean_inc(v_a_1552_);
lean_inc_ref(v_a_1551_);
v___x_1556_ = lean_apply_5(v_p_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, lean_box(0));
return v___x_1556_;
}
}
LEAN_EXPORT void l_Lean_Parser_withoutPosition_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1550_ = stack[0].m_obj;
lean_object* v_a_1551_ = stack[1].m_obj;
lean_object* v_a_1552_ = stack[2].m_obj;
lean_object* v_a_1553_ = stack[3].m_obj;
lean_object* v_a_1554_ = stack[4].m_obj;
lean_object* v_res_1557_;
v_res_1557_ = l_Lean_Parser_withoutPosition_parenthesizer(v_p_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
stack->m_obj
 = v_res_1557_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object* v_p_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Parser_withoutPosition_parenthesizer(v_p_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1564_;
}
}
lean_object* l_Lean_Parser_withForbidden_formatter___redArg(lean_object* v_p_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1571_; 
lean_inc(v_a_1569_);
lean_inc_ref(v_a_1568_);
lean_inc(v_a_1567_);
lean_inc_ref(v_a_1566_);
v___x_1571_ = lean_apply_5(v_p_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, lean_box(0));
return v___x_1571_;
}
}
LEAN_EXPORT void l_Lean_Parser_withForbidden_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1565_ = stack[0].m_obj;
lean_object* v_a_1566_ = stack[1].m_obj;
lean_object* v_a_1567_ = stack[2].m_obj;
lean_object* v_a_1568_ = stack[3].m_obj;
lean_object* v_a_1569_ = stack[4].m_obj;
lean_object* v_res_1572_;
v_res_1572_ = l_Lean_Parser_withForbidden_formatter___redArg(v_p_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
stack->m_obj
 = v_res_1572_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg___boxed(lean_object* v_p_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Parser_withForbidden_formatter___redArg(v_p_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1579_;
}
}
lean_object* l_Lean_Parser_withForbidden_formatter(lean_object* v_tk_1580_, lean_object* v_p_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
v___x_1587_ = lean_apply_5(v_p_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, lean_box(0));
return v___x_1587_;
}
}
LEAN_EXPORT void l_Lean_Parser_withForbidden_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_1580_ = stack[0].m_obj;
lean_object* v_p_1581_ = stack[1].m_obj;
lean_object* v_a_1582_ = stack[2].m_obj;
lean_object* v_a_1583_ = stack[3].m_obj;
lean_object* v_a_1584_ = stack[4].m_obj;
lean_object* v_a_1585_ = stack[5].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l_Lean_Parser_withForbidden_formatter(v_tk_1580_, v_p_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___boxed(lean_object* v_tk_1589_, lean_object* v_p_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Parser_withForbidden_formatter(v_tk_1589_, v_p_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec_ref(v_tk_1589_);
return v_res_1596_;
}
}
lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg(lean_object* v_p_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; 
lean_inc(v_a_1601_);
lean_inc_ref(v_a_1600_);
lean_inc(v_a_1599_);
lean_inc_ref(v_a_1598_);
v___x_1603_ = lean_apply_5(v_p_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, lean_box(0));
return v___x_1603_;
}
}
LEAN_EXPORT void l_Lean_Parser_withForbidden_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1597_ = stack[0].m_obj;
lean_object* v_a_1598_ = stack[1].m_obj;
lean_object* v_a_1599_ = stack[2].m_obj;
lean_object* v_a_1600_ = stack[3].m_obj;
lean_object* v_a_1601_ = stack[4].m_obj;
lean_object* v_res_1604_;
v_res_1604_ = l_Lean_Parser_withForbidden_parenthesizer___redArg(v_p_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
stack->m_obj
 = v_res_1604_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg___boxed(lean_object* v_p_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Parser_withForbidden_parenthesizer___redArg(v_p_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1611_;
}
}
lean_object* l_Lean_Parser_withForbidden_parenthesizer(lean_object* v_tk_1612_, lean_object* v_p_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; 
lean_inc(v_a_1617_);
lean_inc_ref(v_a_1616_);
lean_inc(v_a_1615_);
lean_inc_ref(v_a_1614_);
v___x_1619_ = lean_apply_5(v_p_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, lean_box(0));
return v___x_1619_;
}
}
LEAN_EXPORT void l_Lean_Parser_withForbidden_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_1612_ = stack[0].m_obj;
lean_object* v_p_1613_ = stack[1].m_obj;
lean_object* v_a_1614_ = stack[2].m_obj;
lean_object* v_a_1615_ = stack[3].m_obj;
lean_object* v_a_1616_ = stack[4].m_obj;
lean_object* v_a_1617_ = stack[5].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l_Lean_Parser_withForbidden_parenthesizer(v_tk_1612_, v_p_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
stack->m_obj
 = v_res_1620_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object* v_tk_1621_, lean_object* v_p_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Parser_withForbidden_parenthesizer(v_tk_1621_, v_p_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec_ref(v_tk_1621_);
return v_res_1628_;
}
}
lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object* v_p_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc(v_a_1633_);
lean_inc_ref(v_a_1632_);
lean_inc(v_a_1631_);
lean_inc_ref(v_a_1630_);
v___x_1635_ = lean_apply_5(v_p_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, lean_box(0));
return v___x_1635_;
}
}
LEAN_EXPORT void l_Lean_Parser_withoutForbidden_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1629_ = stack[0].m_obj;
lean_object* v_a_1630_ = stack[1].m_obj;
lean_object* v_a_1631_ = stack[2].m_obj;
lean_object* v_a_1632_ = stack[3].m_obj;
lean_object* v_a_1633_ = stack[4].m_obj;
lean_object* v_res_1636_;
v_res_1636_ = l_Lean_Parser_withoutForbidden_formatter(v_p_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter___boxed(lean_object* v_p_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Parser_withoutForbidden_formatter(v_p_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1643_;
}
}
lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object* v_p_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
lean_inc(v_a_1648_);
lean_inc_ref(v_a_1647_);
lean_inc(v_a_1646_);
lean_inc_ref(v_a_1645_);
v___x_1650_ = lean_apply_5(v_p_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, lean_box(0));
return v___x_1650_;
}
}
LEAN_EXPORT void l_Lean_Parser_withoutForbidden_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1644_ = stack[0].m_obj;
lean_object* v_a_1645_ = stack[1].m_obj;
lean_object* v_a_1646_ = stack[2].m_obj;
lean_object* v_a_1647_ = stack[3].m_obj;
lean_object* v_a_1648_ = stack[4].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l_Lean_Parser_withoutForbidden_parenthesizer(v_p_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer___boxed(lean_object* v_p_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Parser_withoutForbidden_parenthesizer(v_p_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
return v_res_1658_;
}
}
lean_object* l_Lean_Parser_incQuotDepth_formatter(lean_object* v_p_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; 
lean_inc(v_a_1663_);
lean_inc_ref(v_a_1662_);
lean_inc(v_a_1661_);
lean_inc_ref(v_a_1660_);
v___x_1665_ = lean_apply_5(v_p_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, lean_box(0));
return v___x_1665_;
}
}
LEAN_EXPORT void l_Lean_Parser_incQuotDepth_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1659_ = stack[0].m_obj;
lean_object* v_a_1660_ = stack[1].m_obj;
lean_object* v_a_1661_ = stack[2].m_obj;
lean_object* v_a_1662_ = stack[3].m_obj;
lean_object* v_a_1663_ = stack[4].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l_Lean_Parser_incQuotDepth_formatter(v_p_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter___boxed(lean_object* v_p_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Parser_incQuotDepth_formatter(v_p_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
return v_res_1673_;
}
}
lean_object* l_Lean_Parser_incQuotDepth_parenthesizer(lean_object* v_p_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; 
lean_inc(v_a_1678_);
lean_inc_ref(v_a_1677_);
lean_inc(v_a_1676_);
lean_inc_ref(v_a_1675_);
v___x_1680_ = lean_apply_5(v_p_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, lean_box(0));
return v___x_1680_;
}
}
LEAN_EXPORT void l_Lean_Parser_incQuotDepth_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1674_ = stack[0].m_obj;
lean_object* v_a_1675_ = stack[1].m_obj;
lean_object* v_a_1676_ = stack[2].m_obj;
lean_object* v_a_1677_ = stack[3].m_obj;
lean_object* v_a_1678_ = stack[4].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l_Lean_Parser_incQuotDepth_parenthesizer(v_p_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer___boxed(lean_object* v_p_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Parser_incQuotDepth_parenthesizer(v_p_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
return v_res_1688_;
}
}
lean_object* l_Lean_Parser_suppressInsideQuot_formatter(lean_object* v_00___1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
lean_inc(v_a_1693_);
lean_inc_ref(v_a_1692_);
lean_inc(v_a_1691_);
lean_inc_ref(v_a_1690_);
v___x_1695_ = lean_apply_5(v_00___1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, lean_box(0));
return v___x_1695_;
}
}
LEAN_EXPORT void l_Lean_Parser_suppressInsideQuot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_00___1689_ = stack[0].m_obj;
lean_object* v_a_1690_ = stack[1].m_obj;
lean_object* v_a_1691_ = stack[2].m_obj;
lean_object* v_a_1692_ = stack[3].m_obj;
lean_object* v_a_1693_ = stack[4].m_obj;
lean_object* v_res_1696_;
v_res_1696_ = l_Lean_Parser_suppressInsideQuot_formatter(v_00___1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter___boxed(lean_object* v_00___1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Parser_suppressInsideQuot_formatter(v_00___1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1703_;
}
}
lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer(lean_object* v_00___1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; 
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
v___x_1710_ = lean_apply_5(v_00___1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
return v___x_1710_;
}
}
LEAN_EXPORT void l_Lean_Parser_suppressInsideQuot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_00___1704_ = stack[0].m_obj;
lean_object* v_a_1705_ = stack[1].m_obj;
lean_object* v_a_1706_ = stack[2].m_obj;
lean_object* v_a_1707_ = stack[3].m_obj;
lean_object* v_a_1708_ = stack[4].m_obj;
lean_object* v_res_1711_;
v_res_1711_ = l_Lean_Parser_suppressInsideQuot_parenthesizer(v_00___1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
stack->m_obj
 = v_res_1711_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer___boxed(lean_object* v_00___1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Parser_suppressInsideQuot_parenthesizer(v_00___1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
return v_res_1718_;
}
}
lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg(lean_object* v_p_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; 
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
v___x_1725_ = lean_apply_5(v_p_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, lean_box(0));
return v___x_1725_;
}
}
LEAN_EXPORT void l_Lean_Parser_evalInsideQuot_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1719_ = stack[0].m_obj;
lean_object* v_a_1720_ = stack[1].m_obj;
lean_object* v_a_1721_ = stack[2].m_obj;
lean_object* v_a_1722_ = stack[3].m_obj;
lean_object* v_a_1723_ = stack[4].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l_Lean_Parser_evalInsideQuot_formatter___redArg(v_p_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg___boxed(lean_object* v_p_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Parser_evalInsideQuot_formatter___redArg(v_p_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1733_;
}
}
lean_object* l_Lean_Parser_evalInsideQuot_formatter(lean_object* v_declName_1734_, lean_object* v_p_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; 
lean_inc(v_a_1739_);
lean_inc_ref(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_a_1736_);
v___x_1741_ = lean_apply_5(v_p_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, lean_box(0));
return v___x_1741_;
}
}
LEAN_EXPORT void l_Lean_Parser_evalInsideQuot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1734_ = stack[0].m_obj;
lean_object* v_p_1735_ = stack[1].m_obj;
lean_object* v_a_1736_ = stack[2].m_obj;
lean_object* v_a_1737_ = stack[3].m_obj;
lean_object* v_a_1738_ = stack[4].m_obj;
lean_object* v_a_1739_ = stack[5].m_obj;
lean_object* v_res_1742_;
v_res_1742_ = l_Lean_Parser_evalInsideQuot_formatter(v_declName_1734_, v_p_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
stack->m_obj
 = v_res_1742_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___boxed(lean_object* v_declName_1743_, lean_object* v_p_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Parser_evalInsideQuot_formatter(v_declName_1743_, v_p_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_declName_1743_);
return v_res_1750_;
}
}
lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(lean_object* v_p_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; 
lean_inc(v_a_1755_);
lean_inc_ref(v_a_1754_);
lean_inc(v_a_1753_);
lean_inc_ref(v_a_1752_);
v___x_1757_ = lean_apply_5(v_p_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, lean_box(0));
return v___x_1757_;
}
}
LEAN_EXPORT void l_Lean_Parser_evalInsideQuot_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1751_ = stack[0].m_obj;
lean_object* v_a_1752_ = stack[1].m_obj;
lean_object* v_a_1753_ = stack[2].m_obj;
lean_object* v_a_1754_ = stack[3].m_obj;
lean_object* v_a_1755_ = stack[4].m_obj;
lean_object* v_res_1758_;
v_res_1758_ = l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(v_p_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
stack->m_obj
 = v_res_1758_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg___boxed(lean_object* v_p_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(v_p_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1765_;
}
}
lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer(lean_object* v_declName_1766_, lean_object* v_p_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1773_; 
lean_inc(v_a_1771_);
lean_inc_ref(v_a_1770_);
lean_inc(v_a_1769_);
lean_inc_ref(v_a_1768_);
v___x_1773_ = lean_apply_5(v_p_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, lean_box(0));
return v___x_1773_;
}
}
LEAN_EXPORT void l_Lean_Parser_evalInsideQuot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1766_ = stack[0].m_obj;
lean_object* v_p_1767_ = stack[1].m_obj;
lean_object* v_a_1768_ = stack[2].m_obj;
lean_object* v_a_1769_ = stack[3].m_obj;
lean_object* v_a_1770_ = stack[4].m_obj;
lean_object* v_a_1771_ = stack[5].m_obj;
lean_object* v_res_1774_;
v_res_1774_ = l_Lean_Parser_evalInsideQuot_parenthesizer(v_declName_1766_, v_p_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
stack->m_obj
 = v_res_1774_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(lean_object* v_declName_1775_, lean_object* v_p_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Parser_evalInsideQuot_parenthesizer(v_declName_1775_, v_p_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_declName_1775_);
return v_res_1782_;
}
}
lean_object* l_Lean_Parser_withOpen_formatter(lean_object* v_p_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
lean_inc(v_a_1787_);
lean_inc_ref(v_a_1786_);
lean_inc(v_a_1785_);
lean_inc_ref(v_a_1784_);
v___x_1789_ = lean_apply_5(v_p_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, lean_box(0));
return v___x_1789_;
}
}
LEAN_EXPORT void l_Lean_Parser_withOpen_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1783_ = stack[0].m_obj;
lean_object* v_a_1784_ = stack[1].m_obj;
lean_object* v_a_1785_ = stack[2].m_obj;
lean_object* v_a_1786_ = stack[3].m_obj;
lean_object* v_a_1787_ = stack[4].m_obj;
lean_object* v_res_1790_;
v_res_1790_ = l_Lean_Parser_withOpen_formatter(v_p_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
stack->m_obj
 = v_res_1790_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter___boxed(lean_object* v_p_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Parser_withOpen_formatter(v_p_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1797_;
}
}
lean_object* l_Lean_Parser_withOpen_parenthesizer(lean_object* v_p_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; 
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
lean_inc(v_a_1800_);
lean_inc_ref(v_a_1799_);
v___x_1804_ = lean_apply_5(v_p_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, lean_box(0));
return v___x_1804_;
}
}
LEAN_EXPORT void l_Lean_Parser_withOpen_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1798_ = stack[0].m_obj;
lean_object* v_a_1799_ = stack[1].m_obj;
lean_object* v_a_1800_ = stack[2].m_obj;
lean_object* v_a_1801_ = stack[3].m_obj;
lean_object* v_a_1802_ = stack[4].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l_Lean_Parser_withOpen_parenthesizer(v_p_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer___boxed(lean_object* v_p_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Parser_withOpen_parenthesizer(v_p_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1812_;
}
}
lean_object* l_Lean_Parser_withOpenDecl_formatter(lean_object* v_p_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; 
lean_inc(v_a_1817_);
lean_inc_ref(v_a_1816_);
lean_inc(v_a_1815_);
lean_inc_ref(v_a_1814_);
v___x_1819_ = lean_apply_5(v_p_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, lean_box(0));
return v___x_1819_;
}
}
LEAN_EXPORT void l_Lean_Parser_withOpenDecl_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1813_ = stack[0].m_obj;
lean_object* v_a_1814_ = stack[1].m_obj;
lean_object* v_a_1815_ = stack[2].m_obj;
lean_object* v_a_1816_ = stack[3].m_obj;
lean_object* v_a_1817_ = stack[4].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Lean_Parser_withOpenDecl_formatter(v_p_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter___boxed(lean_object* v_p_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Parser_withOpenDecl_formatter(v_p_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
return v_res_1827_;
}
}
lean_object* l_Lean_Parser_withOpenDecl_parenthesizer(lean_object* v_p_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
lean_inc(v_a_1832_);
lean_inc_ref(v_a_1831_);
lean_inc(v_a_1830_);
lean_inc_ref(v_a_1829_);
v___x_1834_ = lean_apply_5(v_p_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, lean_box(0));
return v___x_1834_;
}
}
LEAN_EXPORT void l_Lean_Parser_withOpenDecl_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1828_ = stack[0].m_obj;
lean_object* v_a_1829_ = stack[1].m_obj;
lean_object* v_a_1830_ = stack[2].m_obj;
lean_object* v_a_1831_ = stack[3].m_obj;
lean_object* v_a_1832_ = stack[4].m_obj;
lean_object* v_res_1835_;
v_res_1835_ = l_Lean_Parser_withOpenDecl_parenthesizer(v_p_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
stack->m_obj
 = v_res_1835_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer___boxed(lean_object* v_p_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Parser_withOpenDecl_parenthesizer(v_p_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1842_;
}
}
lean_object* l_Lean_Parser_withSetOption_formatter(lean_object* v_p_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1849_; 
lean_inc(v_a_1847_);
lean_inc_ref(v_a_1846_);
lean_inc(v_a_1845_);
lean_inc_ref(v_a_1844_);
v___x_1849_ = lean_apply_5(v_p_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, lean_box(0));
return v___x_1849_;
}
}
LEAN_EXPORT void l_Lean_Parser_withSetOption_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1843_ = stack[0].m_obj;
lean_object* v_a_1844_ = stack[1].m_obj;
lean_object* v_a_1845_ = stack[2].m_obj;
lean_object* v_a_1846_ = stack[3].m_obj;
lean_object* v_a_1847_ = stack[4].m_obj;
lean_object* v_res_1850_;
v_res_1850_ = l_Lean_Parser_withSetOption_formatter(v_p_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption_formatter___boxed(lean_object* v_p_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Parser_withSetOption_formatter(v_p_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
return v_res_1857_;
}
}
lean_object* l_Lean_Parser_withSetOption_parenthesizer(lean_object* v_p_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1864_; 
lean_inc(v_a_1862_);
lean_inc_ref(v_a_1861_);
lean_inc(v_a_1860_);
lean_inc_ref(v_a_1859_);
v___x_1864_ = lean_apply_5(v_p_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, lean_box(0));
return v___x_1864_;
}
}
LEAN_EXPORT void l_Lean_Parser_withSetOption_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1858_ = stack[0].m_obj;
lean_object* v_a_1859_ = stack[1].m_obj;
lean_object* v_a_1860_ = stack[2].m_obj;
lean_object* v_a_1861_ = stack[3].m_obj;
lean_object* v_a_1862_ = stack[4].m_obj;
lean_object* v_res_1865_;
v_res_1865_ = l_Lean_Parser_withSetOption_parenthesizer(v_p_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
stack->m_obj
 = v_res_1865_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption_parenthesizer___boxed(lean_object* v_p_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Parser_withSetOption_parenthesizer(v_p_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
return v_res_1872_;
}
}
lean_object* l_Lean_Parser_withSetOptionValue_formatter(lean_object* v_p_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1879_; 
lean_inc(v_a_1877_);
lean_inc_ref(v_a_1876_);
lean_inc(v_a_1875_);
lean_inc_ref(v_a_1874_);
v___x_1879_ = lean_apply_5(v_p_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, lean_box(0));
return v___x_1879_;
}
}
LEAN_EXPORT void l_Lean_Parser_withSetOptionValue_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1873_ = stack[0].m_obj;
lean_object* v_a_1874_ = stack[1].m_obj;
lean_object* v_a_1875_ = stack[2].m_obj;
lean_object* v_a_1876_ = stack[3].m_obj;
lean_object* v_a_1877_ = stack[4].m_obj;
lean_object* v_res_1880_;
v_res_1880_ = l_Lean_Parser_withSetOptionValue_formatter(v_p_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
stack->m_obj
 = v_res_1880_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue_formatter___boxed(lean_object* v_p_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Parser_withSetOptionValue_formatter(v_p_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1887_;
}
}
lean_object* l_Lean_Parser_withSetOptionValue_parenthesizer(lean_object* v_p_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; 
lean_inc(v_a_1892_);
lean_inc_ref(v_a_1891_);
lean_inc(v_a_1890_);
lean_inc_ref(v_a_1889_);
v___x_1894_ = lean_apply_5(v_p_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, lean_box(0));
return v___x_1894_;
}
}
LEAN_EXPORT void l_Lean_Parser_withSetOptionValue_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1888_ = stack[0].m_obj;
lean_object* v_a_1889_ = stack[1].m_obj;
lean_object* v_a_1890_ = stack[2].m_obj;
lean_object* v_a_1891_ = stack[3].m_obj;
lean_object* v_a_1892_ = stack[4].m_obj;
lean_object* v_res_1895_;
v_res_1895_ = l_Lean_Parser_withSetOptionValue_parenthesizer(v_p_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue_parenthesizer___boxed(lean_object* v_p_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Parser_withSetOptionValue_parenthesizer(v_p_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1902_;
}
}
lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg(lean_object* v_p_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; 
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
v___x_1909_ = lean_apply_5(v_p_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, lean_box(0));
return v___x_1909_;
}
}
LEAN_EXPORT void l_Lean_Parser_dbgTraceState_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1903_ = stack[0].m_obj;
lean_object* v_a_1904_ = stack[1].m_obj;
lean_object* v_a_1905_ = stack[2].m_obj;
lean_object* v_a_1906_ = stack[3].m_obj;
lean_object* v_a_1907_ = stack[4].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_Parser_dbgTraceState_formatter___redArg(v_p_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg___boxed(lean_object* v_p_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Parser_dbgTraceState_formatter___redArg(v_p_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
return v_res_1917_;
}
}
lean_object* l_Lean_Parser_dbgTraceState_formatter(lean_object* v_label_1918_, lean_object* v_p_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; 
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
v___x_1925_ = lean_apply_5(v_p_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, lean_box(0));
return v___x_1925_;
}
}
LEAN_EXPORT void l_Lean_Parser_dbgTraceState_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_1918_ = stack[0].m_obj;
lean_object* v_p_1919_ = stack[1].m_obj;
lean_object* v_a_1920_ = stack[2].m_obj;
lean_object* v_a_1921_ = stack[3].m_obj;
lean_object* v_a_1922_ = stack[4].m_obj;
lean_object* v_a_1923_ = stack[5].m_obj;
lean_object* v_res_1926_;
v_res_1926_ = l_Lean_Parser_dbgTraceState_formatter(v_label_1918_, v_p_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___boxed(lean_object* v_label_1927_, lean_object* v_p_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Parser_dbgTraceState_formatter(v_label_1927_, v_p_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec_ref(v_label_1927_);
return v_res_1934_;
}
}
lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg(lean_object* v_p_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; 
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_1941_ = lean_apply_5(v_p_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
return v___x_1941_;
}
}
LEAN_EXPORT void l_Lean_Parser_dbgTraceState_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1935_ = stack[0].m_obj;
lean_object* v_a_1936_ = stack[1].m_obj;
lean_object* v_a_1937_ = stack[2].m_obj;
lean_object* v_a_1938_ = stack[3].m_obj;
lean_object* v_a_1939_ = stack[4].m_obj;
lean_object* v_res_1942_;
v_res_1942_ = l_Lean_Parser_dbgTraceState_parenthesizer___redArg(v_p_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
stack->m_obj
 = v_res_1942_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg___boxed(lean_object* v_p_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Parser_dbgTraceState_parenthesizer___redArg(v_p_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
return v_res_1949_;
}
}
lean_object* l_Lean_Parser_dbgTraceState_parenthesizer(lean_object* v_label_1950_, lean_object* v_p_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1957_; 
lean_inc(v_a_1955_);
lean_inc_ref(v_a_1954_);
lean_inc(v_a_1953_);
lean_inc_ref(v_a_1952_);
v___x_1957_ = lean_apply_5(v_p_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, lean_box(0));
return v___x_1957_;
}
}
LEAN_EXPORT void l_Lean_Parser_dbgTraceState_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_1950_ = stack[0].m_obj;
lean_object* v_p_1951_ = stack[1].m_obj;
lean_object* v_a_1952_ = stack[2].m_obj;
lean_object* v_a_1953_ = stack[3].m_obj;
lean_object* v_a_1954_ = stack[4].m_obj;
lean_object* v_a_1955_ = stack[5].m_obj;
lean_object* v_res_1958_;
v_res_1958_ = l_Lean_Parser_dbgTraceState_parenthesizer(v_label_1950_, v_p_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
stack->m_obj
 = v_res_1958_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___boxed(lean_object* v_label_1959_, lean_object* v_p_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Parser_dbgTraceState_parenthesizer(v_label_1959_, v_p_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec_ref(v_label_1959_);
return v_res_1966_;
}
}
lean_object* l_Lean_Parser_optional_formatter(lean_object* v_p_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1979_ = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__1));
v___x_1980_ = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__3));
v___x_1981_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_1981_, 0, v___x_1979_);
lean_closure_set(v___x_1981_, 1, v_p_1973_);
lean_closure_set(v___x_1981_, 2, v___x_1980_);
v___x_1982_ = l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(v___x_1981_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
return v___x_1982_;
}
}
LEAN_EXPORT void l_Lean_Parser_optional_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1973_ = stack[0].m_obj;
lean_object* v_a_1974_ = stack[1].m_obj;
lean_object* v_a_1975_ = stack[2].m_obj;
lean_object* v_a_1976_ = stack[3].m_obj;
lean_object* v_a_1977_ = stack[4].m_obj;
lean_object* v_res_1983_;
v_res_1983_ = l_Lean_Parser_optional_formatter(v_p_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
stack->m_obj
 = v_res_1983_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object* v_p_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Parser_optional_formatter(v_p_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
return v_res_1990_;
}
}
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object* v_p_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__1));
v___x_2000_ = ((lean_object*)(l_Lean_Parser_optional_parenthesizer___closed__0));
v___x_2001_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2001_, 0, v___x_1999_);
lean_closure_set(v___x_2001_, 1, v_p_1993_);
lean_closure_set(v___x_2001_, 2, v___x_2000_);
v___x_2002_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___x_2001_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
return v___x_2002_;
}
}
LEAN_EXPORT void l_Lean_Parser_optional_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1993_ = stack[0].m_obj;
lean_object* v_a_1994_ = stack[1].m_obj;
lean_object* v_a_1995_ = stack[2].m_obj;
lean_object* v_a_1996_ = stack[3].m_obj;
lean_object* v_a_1997_ = stack[4].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l_Lean_Parser_optional_parenthesizer(v_p_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
stack->m_obj
 = v_res_2003_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object* v_p_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Parser_optional_parenthesizer(v_p_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
return v_res_2010_;
}
}
static lean_object* _init_l_Lean_Parser_optional___closed__0(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__2));
v___x_2012_ = l_Lean_Parser_symbol(v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional(lean_object* v_p_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = ((lean_object*)(l_Lean_Parser_optional_formatter___closed__1));
v___x_2015_ = lean_obj_once(&l_Lean_Parser_optional___closed__0, &l_Lean_Parser_optional___closed__0_once, _init_l_Lean_Parser_optional___closed__0);
v___x_2016_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_2014_, v_p_2013_, v___x_2015_);
v___x_2017_ = l_Lean_Parser_optionalNoAntiquot(v___x_2016_);
return v___x_2017_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1(){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__0));
v___x_2025_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___closed__1));
v___x_2026_ = l_Lean_addBuiltinDocString(v___x_2024_, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2027_;
v_res_2027_ = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1___boxed(lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
return v_res_2029_;
}
}
lean_object* l_Lean_Parser_many_formatter(lean_object* v_p_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
v___x_2042_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__2));
v___x_2043_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_2043_, 0, v___x_2041_);
lean_closure_set(v___x_2043_, 1, v_p_2035_);
lean_closure_set(v___x_2043_, 2, v___x_2042_);
v___x_2044_ = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(v___x_2043_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
return v___x_2044_;
}
}
LEAN_EXPORT void l_Lean_Parser_many_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2035_ = stack[0].m_obj;
lean_object* v_a_2036_ = stack[1].m_obj;
lean_object* v_a_2037_ = stack[2].m_obj;
lean_object* v_a_2038_ = stack[3].m_obj;
lean_object* v_a_2039_ = stack[4].m_obj;
lean_object* v_res_2045_;
v_res_2045_ = l_Lean_Parser_many_formatter(v_p_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter___boxed(lean_object* v_p_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Parser_many_formatter(v_p_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
return v_res_2052_;
}
}
lean_object* l_Lean_Parser_many_parenthesizer(lean_object* v_p_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
v___x_2062_ = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
v___x_2063_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2063_, 0, v___x_2061_);
lean_closure_set(v___x_2063_, 1, v_p_2055_);
lean_closure_set(v___x_2063_, 2, v___x_2062_);
v___x_2064_ = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(v___x_2063_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
return v___x_2064_;
}
}
LEAN_EXPORT void l_Lean_Parser_many_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2055_ = stack[0].m_obj;
lean_object* v_a_2056_ = stack[1].m_obj;
lean_object* v_a_2057_ = stack[2].m_obj;
lean_object* v_a_2058_ = stack[3].m_obj;
lean_object* v_a_2059_ = stack[4].m_obj;
lean_object* v_res_2065_;
v_res_2065_ = l_Lean_Parser_many_parenthesizer(v_p_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
stack->m_obj
 = v_res_2065_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object* v_p_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Parser_many_parenthesizer(v_p_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_Parser_many___closed__0(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__2));
v___x_2074_ = l_Lean_Parser_symbol(v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many(lean_object* v_p_2075_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
v___x_2077_ = lean_obj_once(&l_Lean_Parser_many___closed__0, &l_Lean_Parser_many___closed__0_once, _init_l_Lean_Parser_many___closed__0);
v___x_2078_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_2076_, v_p_2075_, v___x_2077_);
v___x_2079_ = l_Lean_Parser_manyNoAntiquot(v___x_2078_);
return v___x_2079_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1(){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__0));
v___x_2087_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___closed__1));
v___x_2088_ = l_Lean_addBuiltinDocString(v___x_2086_, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2089_;
v_res_2089_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
stack->m_obj
 = v_res_2089_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1___boxed(lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
return v_res_2091_;
}
}
lean_object* l_Lean_Parser_many1_formatter(lean_object* v_p_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2098_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
v___x_2099_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__2));
v___x_2100_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed), 8, 3);
lean_closure_set(v___x_2100_, 0, v___x_2098_);
lean_closure_set(v___x_2100_, 1, v_p_2092_);
lean_closure_set(v___x_2100_, 2, v___x_2099_);
v___x_2101_ = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(v___x_2100_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
return v___x_2101_;
}
}
LEAN_EXPORT void l_Lean_Parser_many1_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2092_ = stack[0].m_obj;
lean_object* v_a_2093_ = stack[1].m_obj;
lean_object* v_a_2094_ = stack[2].m_obj;
lean_object* v_a_2095_ = stack[3].m_obj;
lean_object* v_a_2096_ = stack[4].m_obj;
lean_object* v_res_2102_;
v_res_2102_ = l_Lean_Parser_many1_formatter(v_p_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
stack->m_obj
 = v_res_2102_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object* v_p_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Parser_many1_formatter(v_p_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
return v_res_2109_;
}
}
lean_object* l_Lean_Parser_many1_parenthesizer(lean_object* v_p_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
v___x_2117_ = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
v___x_2118_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2118_, 0, v___x_2116_);
lean_closure_set(v___x_2118_, 1, v_p_2110_);
lean_closure_set(v___x_2118_, 2, v___x_2117_);
v___x_2119_ = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(v___x_2118_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2119_;
}
}
LEAN_EXPORT void l_Lean_Parser_many1_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2110_ = stack[0].m_obj;
lean_object* v_a_2111_ = stack[1].m_obj;
lean_object* v_a_2112_ = stack[2].m_obj;
lean_object* v_a_2113_ = stack[3].m_obj;
lean_object* v_a_2114_ = stack[4].m_obj;
lean_object* v_res_2120_;
v_res_2120_ = l_Lean_Parser_many1_parenthesizer(v_p_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
stack->m_obj
 = v_res_2120_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object* v_p_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_Parser_many1_parenthesizer(v_p_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1(lean_object* v_p_2128_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = ((lean_object*)(l_Lean_Parser_many_formatter___closed__1));
v___x_2130_ = lean_obj_once(&l_Lean_Parser_many___closed__0, &l_Lean_Parser_many___closed__0_once, _init_l_Lean_Parser_many___closed__0);
v___x_2131_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_2129_, v_p_2128_, v___x_2130_);
v___x_2132_ = l_Lean_Parser_many1NoAntiquot(v___x_2131_);
return v___x_2132_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1(){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__1));
v___x_2141_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___closed__2));
v___x_2142_ = l_Lean_addBuiltinDocString(v___x_2140_, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2143_;
v_res_2143_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
stack->m_obj
 = v_res_2143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1___boxed(lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
return v_res_2145_;
}
}
lean_object* l_Lean_Parser_ident_formatter(lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__2));
v___x_2162_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___boxed), 5, 0);
v___x_2163_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2161_, v___x_2162_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v___x_2163_;
}
}
LEAN_EXPORT void l_Lean_Parser_ident_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2156_ = stack[0].m_obj;
lean_object* v_a_2157_ = stack[1].m_obj;
lean_object* v_a_2158_ = stack[2].m_obj;
lean_object* v_a_2159_ = stack[3].m_obj;
lean_object* v_res_2164_;
v_res_2164_ = l_Lean_Parser_ident_formatter(v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
stack->m_obj
 = v_res_2164_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Parser_ident_formatter(v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2170_;
}
}
lean_object* l_Lean_Parser_ident_parenthesizer(lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l_Lean_Parser_ident_parenthesizer___closed__0));
v___x_2184_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 5, 0);
v___x_2185_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2183_, v___x_2184_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2185_;
}
}
LEAN_EXPORT void l_Lean_Parser_ident_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2178_ = stack[0].m_obj;
lean_object* v_a_2179_ = stack[1].m_obj;
lean_object* v_a_2180_ = stack[2].m_obj;
lean_object* v_a_2181_ = stack[3].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l_Lean_Parser_ident_parenthesizer(v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Parser_ident_parenthesizer(v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2192_;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__0(void){
_start:
{
uint8_t v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2193_ = 0;
v___x_2194_ = 1;
v___x_2195_ = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__1));
v___x_2196_ = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__0));
v___x_2197_ = l_Lean_Parser_mkAntiquot(v___x_2196_, v___x_2195_, v___x_2194_, v___x_2193_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_Parser_ident___closed__1(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = l_Lean_Parser_identNoAntiquot;
v___x_2199_ = lean_obj_once(&l_Lean_Parser_ident___closed__0, &l_Lean_Parser_ident___closed__0_once, _init_l_Lean_Parser_ident___closed__0);
v___x_2200_ = l_Lean_Parser_withAntiquot(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_Parser_ident(void){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_obj_once(&l_Lean_Parser_ident___closed__1, &l_Lean_Parser_ident___closed__1_once, _init_l_Lean_Parser_ident___closed__1);
return v___x_2201_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1(){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__0));
v___x_2209_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___closed__1));
v___x_2210_ = l_Lean_addBuiltinDocString(v___x_2208_, v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2211_;
v_res_2211_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
stack->m_obj
 = v_res_2211_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1___boxed(lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
return v_res_2213_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter___boxed), 5, 0);
v___f_2218_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
v___x_2219_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2219_, 0, v___f_2218_);
lean_closure_set(v___x_2219_, 1, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2, &l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2_once, _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__2);
v___x_2221_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__1));
v___x_2222_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2222_, 0, v___x_2221_);
lean_closure_set(v___x_2222_, 1, v___x_2220_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3, &l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3_once, _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__3);
v___f_2224_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__0));
v___x_2225_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2225_, 0, v___f_2224_);
lean_closure_set(v___x_2225_, 1, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4, &l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4_once, _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__4);
v___x_2227_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter___boxed), 5, 0);
v___x_2234_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5, &l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5_once, _init_l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__5);
v___x_2235_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_2233_, v___x_2234_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
return v___x_2235_;
}
}
LEAN_EXPORT void l_Lean_Parser_identWithPartialTrailingDot_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2228_ = stack[0].m_obj;
lean_object* v_a_2229_ = stack[1].m_obj;
lean_object* v_a_2230_ = stack[2].m_obj;
lean_object* v_a_2231_ = stack[3].m_obj;
lean_object* v_res_2236_;
v_res_2236_ = l_Lean_Parser_identWithPartialTrailingDot_formatter(v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
stack->m_obj
 = v_res_2236_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter___boxed(lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Parser_identWithPartialTrailingDot_formatter(v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2242_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer___boxed), 5, 0);
v___x_2246_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_2247_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2247_, 0, v___x_2246_);
lean_closure_set(v___x_2247_, 1, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1, &l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1_once, _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__1);
v___x_2249_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__0));
v___x_2250_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2250_, 0, v___x_2249_);
lean_closure_set(v___x_2250_, 1, v___x_2248_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2, &l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2_once, _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__2);
v___x_2252_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
v___x_2253_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2253_, 0, v___x_2252_);
lean_closure_set(v___x_2253_, 1, v___x_2251_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3, &l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3_once, _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__3);
v___x_2255_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
}
lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer___boxed), 5, 0);
v___x_2262_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4, &l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4_once, _init_l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___closed__4);
v___x_2263_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2261_, v___x_2262_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
return v___x_2263_;
}
}
LEAN_EXPORT void l_Lean_Parser_identWithPartialTrailingDot_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2256_ = stack[0].m_obj;
lean_object* v_a_2257_ = stack[1].m_obj;
lean_object* v_a_2258_ = stack[2].m_obj;
lean_object* v_a_2259_ = stack[3].m_obj;
lean_object* v_res_2264_;
v_res_2264_ = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
stack->m_obj
 = v_res_2264_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer___boxed(lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2270_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot___closed__0));
v___x_2273_ = l_Lean_Parser_checkNoWsBefore(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__2(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0));
v___x_2275_ = l_Lean_Parser_symbol(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__3(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_Parser_ident;
v___x_2277_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__1, &l_Lean_Parser_identWithPartialTrailingDot___closed__1_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1);
v___x_2278_ = l_Lean_Parser_andthen(v___x_2277_, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__4(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__3, &l_Lean_Parser_identWithPartialTrailingDot___closed__3_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__3);
v___x_2280_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__2, &l_Lean_Parser_identWithPartialTrailingDot___closed__2_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__2);
v___x_2281_ = l_Lean_Parser_andthen(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__5(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__4, &l_Lean_Parser_identWithPartialTrailingDot___closed__4_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__4);
v___x_2283_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__1, &l_Lean_Parser_identWithPartialTrailingDot___closed__1_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__1);
v___x_2284_ = l_Lean_Parser_andthen(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__6(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__5, &l_Lean_Parser_identWithPartialTrailingDot___closed__5_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__5);
v___x_2286_ = l_Lean_Parser_optional(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot___closed__7(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__6, &l_Lean_Parser_identWithPartialTrailingDot___closed__6_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__6);
v___x_2288_ = l_Lean_Parser_ident;
v___x_2289_ = l_Lean_Parser_andthen(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot(void){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_obj_once(&l_Lean_Parser_identWithPartialTrailingDot___closed__7, &l_Lean_Parser_identWithPartialTrailingDot___closed__7_once, _init_l_Lean_Parser_identWithPartialTrailingDot___closed__7);
return v___x_2290_;
}
}
lean_object* l_Lean_Parser_rawIdent_formatter(lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = ((lean_object*)(l_Lean_Parser_ident_formatter___closed__2));
v___x_2297_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___boxed), 5, 0);
v___x_2298_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2296_, v___x_2297_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
return v___x_2298_;
}
}
LEAN_EXPORT void l_Lean_Parser_rawIdent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2291_ = stack[0].m_obj;
lean_object* v_a_2292_ = stack[1].m_obj;
lean_object* v_a_2293_ = stack[2].m_obj;
lean_object* v_a_2294_ = stack[3].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l_Lean_Parser_rawIdent_formatter(v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter___boxed(lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Parser_rawIdent_formatter(v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2305_;
}
}
lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0(lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_2307_);
return v___x_2311_;
}
}
LEAN_EXPORT void l_Lean_Parser_rawIdent_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2306_ = stack[0].m_obj;
lean_object* v___y_2307_ = stack[1].m_obj;
lean_object* v___y_2308_ = stack[2].m_obj;
lean_object* v___y_2309_ = stack[3].m_obj;
lean_object* v_res_2312_;
v_res_2312_ = l_Lean_Parser_rawIdent_parenthesizer___lam__0(v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
stack->m_obj
 = v_res_2312_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___lam__0___boxed(lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Parser_rawIdent_parenthesizer___lam__0(v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
return v_res_2318_;
}
}
lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___f_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___f_2325_ = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
v___x_2326_ = ((lean_object*)(l_Lean_Parser_ident_parenthesizer___closed__0));
v___x_2327_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2326_, v___f_2325_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
return v___x_2327_;
}
}
LEAN_EXPORT void l_Lean_Parser_rawIdent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2320_ = stack[0].m_obj;
lean_object* v_a_2321_ = stack[1].m_obj;
lean_object* v_a_2322_ = stack[2].m_obj;
lean_object* v_a_2323_ = stack[3].m_obj;
lean_object* v_res_2328_;
v_res_2328_ = l_Lean_Parser_rawIdent_parenthesizer(v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
stack->m_obj
 = v_res_2328_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer___boxed(lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Parser_rawIdent_parenthesizer(v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
return v_res_2334_;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent___closed__0(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = l_Lean_Parser_rawIdentNoAntiquot;
v___x_2336_ = lean_obj_once(&l_Lean_Parser_ident___closed__0, &l_Lean_Parser_ident___closed__0_once, _init_l_Lean_Parser_ident___closed__0);
v___x_2337_ = l_Lean_Parser_withAntiquot(v___x_2336_, v___x_2335_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent(void){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_obj_once(&l_Lean_Parser_rawIdent___closed__0, &l_Lean_Parser_rawIdent___closed__0_once, _init_l_Lean_Parser_rawIdent___closed__0);
return v___x_2338_;
}
}
lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___f_2353_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_formatter___closed__1));
v___x_2354_ = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__2));
v___x_2355_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2354_, v___f_2353_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
return v___x_2355_;
}
}
LEAN_EXPORT void l_Lean_Parser_hygieneInfo_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2348_ = stack[0].m_obj;
lean_object* v_a_2349_ = stack[1].m_obj;
lean_object* v_a_2350_ = stack[2].m_obj;
lean_object* v_a_2351_ = stack[3].m_obj;
lean_object* v_res_2356_;
v_res_2356_ = l_Lean_Parser_hygieneInfo_formatter(v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
stack->m_obj
 = v_res_2356_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___boxed(lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Parser_hygieneInfo_formatter(v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2362_;
}
}
lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___f_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___f_2374_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0));
v___x_2375_ = ((lean_object*)(l_Lean_Parser_hygieneInfo_parenthesizer___closed__0));
v___x_2376_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2375_, v___f_2374_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2376_;
}
}
LEAN_EXPORT void l_Lean_Parser_hygieneInfo_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2369_ = stack[0].m_obj;
lean_object* v_a_2370_ = stack[1].m_obj;
lean_object* v_a_2371_ = stack[2].m_obj;
lean_object* v_a_2372_ = stack[3].m_obj;
lean_object* v_res_2377_;
v_res_2377_ = l_Lean_Parser_hygieneInfo_parenthesizer(v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
stack->m_obj
 = v_res_2377_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer___boxed(lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Parser_hygieneInfo_parenthesizer(v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2383_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo___closed__0(void){
_start:
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2384_ = 0;
v___x_2385_ = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__1));
v___x_2386_ = ((lean_object*)(l_Lean_Parser_hygieneInfo_formatter___closed__0));
v___x_2387_ = l_Lean_Parser_mkAntiquot(v___x_2386_, v___x_2385_, v___x_2384_, v___x_2384_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo___closed__1(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = l_Lean_Parser_hygieneInfoNoAntiquot;
v___x_2389_ = lean_obj_once(&l_Lean_Parser_hygieneInfo___closed__0, &l_Lean_Parser_hygieneInfo___closed__0_once, _init_l_Lean_Parser_hygieneInfo___closed__0);
v___x_2390_ = l_Lean_Parser_withAntiquotAcceptLhs(v___x_2389_, v___x_2388_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo(void){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_obj_once(&l_Lean_Parser_hygieneInfo___closed__1, &l_Lean_Parser_hygieneInfo___closed__1_once, _init_l_Lean_Parser_hygieneInfo___closed__1);
return v___x_2391_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1(){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__0));
v___x_2399_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___closed__1));
v___x_2400_ = l_Lean_addBuiltinDocString(v___x_2398_, v___x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2401_;
v_res_2401_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
stack->m_obj
 = v_res_2401_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1___boxed(lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
return v_res_2403_;
}
}
lean_object* l_Lean_Parser_numLit_formatter(lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__2));
v___x_2420_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___boxed), 5, 0);
v___x_2421_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2419_, v___x_2420_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2421_;
}
}
LEAN_EXPORT void l_Lean_Parser_numLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2414_ = stack[0].m_obj;
lean_object* v_a_2415_ = stack[1].m_obj;
lean_object* v_a_2416_ = stack[2].m_obj;
lean_object* v_a_2417_ = stack[3].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l_Lean_Parser_numLit_formatter(v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Parser_numLit_formatter(v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
return v_res_2428_;
}
}
lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___f_2441_ = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
v___x_2442_ = ((lean_object*)(l_Lean_Parser_numLit_parenthesizer___closed__0));
v___x_2443_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2442_, v___f_2441_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
return v___x_2443_;
}
}
LEAN_EXPORT void l_Lean_Parser_numLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2436_ = stack[0].m_obj;
lean_object* v_a_2437_ = stack[1].m_obj;
lean_object* v_a_2438_ = stack[2].m_obj;
lean_object* v_a_2439_ = stack[3].m_obj;
lean_object* v_res_2444_;
v_res_2444_ = l_Lean_Parser_numLit_parenthesizer(v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
stack->m_obj
 = v_res_2444_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Parser_numLit_parenthesizer(v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2450_;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__0(void){
_start:
{
uint8_t v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2451_ = 0;
v___x_2452_ = 1;
v___x_2453_ = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__1));
v___x_2454_ = ((lean_object*)(l_Lean_Parser_numLit_formatter___closed__0));
v___x_2455_ = l_Lean_Parser_mkAntiquot(v___x_2454_, v___x_2453_, v___x_2452_, v___x_2451_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_Parser_numLit___closed__1(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = l_Lean_Parser_numLitNoAntiquot;
v___x_2457_ = lean_obj_once(&l_Lean_Parser_numLit___closed__0, &l_Lean_Parser_numLit___closed__0_once, _init_l_Lean_Parser_numLit___closed__0);
v___x_2458_ = l_Lean_Parser_withAntiquot(v___x_2457_, v___x_2456_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lean_Parser_numLit(void){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_obj_once(&l_Lean_Parser_numLit___closed__1, &l_Lean_Parser_numLit___closed__1_once, _init_l_Lean_Parser_numLit___closed__1);
return v___x_2459_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1(){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__1));
v___x_2468_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___closed__2));
v___x_2469_ = l_Lean_addBuiltinDocString(v___x_2467_, v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2470_;
v_res_2470_ = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
stack->m_obj
 = v_res_2470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1___boxed(lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
return v_res_2472_;
}
}
static lean_object* _init_l_Lean_Parser_hexnum___closed__2(void){
_start:
{
uint8_t v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2476_ = 0;
v___x_2477_ = 1;
v___x_2478_ = ((lean_object*)(l_Lean_Parser_hexnum___closed__1));
v___x_2479_ = ((lean_object*)(l_Lean_Parser_hexnum___closed__0));
v___x_2480_ = l_Lean_Parser_mkAntiquot(v___x_2479_, v___x_2478_, v___x_2477_, v___x_2476_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lean_Parser_hexnum___closed__3(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = l_Lean_Parser_hexnumNoAntiquot;
v___x_2482_ = lean_obj_once(&l_Lean_Parser_hexnum___closed__2, &l_Lean_Parser_hexnum___closed__2_once, _init_l_Lean_Parser_hexnum___closed__2);
v___x_2483_ = l_Lean_Parser_withAntiquot(v___x_2482_, v___x_2481_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Parser_hexnum(void){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_obj_once(&l_Lean_Parser_hexnum___closed__3, &l_Lean_Parser_hexnum___closed__3_once, _init_l_Lean_Parser_hexnum___closed__3);
return v___x_2484_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1(){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__0));
v___x_2492_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___closed__1));
v___x_2493_ = l_Lean_addBuiltinDocString(v___x_2491_, v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2494_;
v_res_2494_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
stack->m_obj
 = v_res_2494_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1___boxed(lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
return v_res_2496_;
}
}
lean_object* l_Lean_Parser_scientificLit_formatter(lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__2));
v___x_2513_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___boxed), 5, 0);
v___x_2514_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2512_, v___x_2513_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2514_;
}
}
LEAN_EXPORT void l_Lean_Parser_scientificLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2507_ = stack[0].m_obj;
lean_object* v_a_2508_ = stack[1].m_obj;
lean_object* v_a_2509_ = stack[2].m_obj;
lean_object* v_a_2510_ = stack[3].m_obj;
lean_object* v_res_2515_;
v_res_2515_ = l_Lean_Parser_scientificLit_formatter(v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
stack->m_obj
 = v_res_2515_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter___boxed(lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Parser_scientificLit_formatter(v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
return v_res_2521_;
}
}
lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___f_2534_ = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
v___x_2535_ = ((lean_object*)(l_Lean_Parser_scientificLit_parenthesizer___closed__0));
v___x_2536_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2535_, v___f_2534_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
return v___x_2536_;
}
}
LEAN_EXPORT void l_Lean_Parser_scientificLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2529_ = stack[0].m_obj;
lean_object* v_a_2530_ = stack[1].m_obj;
lean_object* v_a_2531_ = stack[2].m_obj;
lean_object* v_a_2532_ = stack[3].m_obj;
lean_object* v_res_2537_;
v_res_2537_ = l_Lean_Parser_scientificLit_parenthesizer(v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
stack->m_obj
 = v_res_2537_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer___boxed(lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Parser_scientificLit_parenthesizer(v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2543_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__0(void){
_start:
{
uint8_t v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2544_ = 0;
v___x_2545_ = 1;
v___x_2546_ = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__1));
v___x_2547_ = ((lean_object*)(l_Lean_Parser_scientificLit_formatter___closed__0));
v___x_2548_ = l_Lean_Parser_mkAntiquot(v___x_2547_, v___x_2546_, v___x_2545_, v___x_2544_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit___closed__1(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = l_Lean_Parser_scientificLitNoAntiquot;
v___x_2550_ = lean_obj_once(&l_Lean_Parser_scientificLit___closed__0, &l_Lean_Parser_scientificLit___closed__0_once, _init_l_Lean_Parser_scientificLit___closed__0);
v___x_2551_ = l_Lean_Parser_withAntiquot(v___x_2550_, v___x_2549_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit(void){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_obj_once(&l_Lean_Parser_scientificLit___closed__1, &l_Lean_Parser_scientificLit___closed__1_once, _init_l_Lean_Parser_scientificLit___closed__1);
return v___x_2552_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1(){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__1));
v___x_2561_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___closed__2));
v___x_2562_ = l_Lean_addBuiltinDocString(v___x_2560_, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2563_;
v_res_2563_ = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1___boxed(lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
return v_res_2565_;
}
}
lean_object* l_Lean_Parser_strLit_formatter(lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__2));
v___x_2582_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___boxed), 5, 0);
v___x_2583_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2581_, v___x_2582_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
return v___x_2583_;
}
}
LEAN_EXPORT void l_Lean_Parser_strLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2576_ = stack[0].m_obj;
lean_object* v_a_2577_ = stack[1].m_obj;
lean_object* v_a_2578_ = stack[2].m_obj;
lean_object* v_a_2579_ = stack[3].m_obj;
lean_object* v_res_2584_;
v_res_2584_ = l_Lean_Parser_strLit_formatter(v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
stack->m_obj
 = v_res_2584_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_Parser_strLit_formatter(v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2590_;
}
}
lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___f_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___f_2603_ = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
v___x_2604_ = ((lean_object*)(l_Lean_Parser_strLit_parenthesizer___closed__0));
v___x_2605_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2604_, v___f_2603_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
return v___x_2605_;
}
}
LEAN_EXPORT void l_Lean_Parser_strLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2598_ = stack[0].m_obj;
lean_object* v_a_2599_ = stack[1].m_obj;
lean_object* v_a_2600_ = stack[2].m_obj;
lean_object* v_a_2601_ = stack[3].m_obj;
lean_object* v_res_2606_;
v_res_2606_ = l_Lean_Parser_strLit_parenthesizer(v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
stack->m_obj
 = v_res_2606_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Parser_strLit_parenthesizer(v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
return v_res_2612_;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__0(void){
_start:
{
uint8_t v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2613_ = 0;
v___x_2614_ = 1;
v___x_2615_ = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__1));
v___x_2616_ = ((lean_object*)(l_Lean_Parser_strLit_formatter___closed__0));
v___x_2617_ = l_Lean_Parser_mkAntiquot(v___x_2616_, v___x_2615_, v___x_2614_, v___x_2613_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Parser_strLit___closed__1(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = l_Lean_Parser_strLitNoAntiquot;
v___x_2619_ = lean_obj_once(&l_Lean_Parser_strLit___closed__0, &l_Lean_Parser_strLit___closed__0_once, _init_l_Lean_Parser_strLit___closed__0);
v___x_2620_ = l_Lean_Parser_withAntiquot(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_Parser_strLit(void){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_obj_once(&l_Lean_Parser_strLit___closed__1, &l_Lean_Parser_strLit___closed__1_once, _init_l_Lean_Parser_strLit___closed__1);
return v___x_2621_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1(){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__1));
v___x_2630_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___closed__2));
v___x_2631_ = l_Lean_addBuiltinDocString(v___x_2629_, v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2632_;
v_res_2632_ = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
stack->m_obj
 = v_res_2632_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1___boxed(lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
return v_res_2634_;
}
}
lean_object* l_Lean_Parser_charLit_formatter(lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__2));
v___x_2651_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___boxed), 5, 0);
v___x_2652_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2650_, v___x_2651_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
return v___x_2652_;
}
}
LEAN_EXPORT void l_Lean_Parser_charLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2645_ = stack[0].m_obj;
lean_object* v_a_2646_ = stack[1].m_obj;
lean_object* v_a_2647_ = stack[2].m_obj;
lean_object* v_a_2648_ = stack[3].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l_Lean_Parser_charLit_formatter(v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter___boxed(lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Parser_charLit_formatter(v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2659_;
}
}
lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___f_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___f_2672_ = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
v___x_2673_ = ((lean_object*)(l_Lean_Parser_charLit_parenthesizer___closed__0));
v___x_2674_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2673_, v___f_2672_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
return v___x_2674_;
}
}
LEAN_EXPORT void l_Lean_Parser_charLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2667_ = stack[0].m_obj;
lean_object* v_a_2668_ = stack[1].m_obj;
lean_object* v_a_2669_ = stack[2].m_obj;
lean_object* v_a_2670_ = stack[3].m_obj;
lean_object* v_res_2675_;
v_res_2675_ = l_Lean_Parser_charLit_parenthesizer(v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
stack->m_obj
 = v_res_2675_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer___boxed(lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Parser_charLit_parenthesizer(v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
return v_res_2681_;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__0(void){
_start:
{
uint8_t v___x_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2682_ = 0;
v___x_2683_ = 1;
v___x_2684_ = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__1));
v___x_2685_ = ((lean_object*)(l_Lean_Parser_charLit_formatter___closed__0));
v___x_2686_ = l_Lean_Parser_mkAntiquot(v___x_2685_, v___x_2684_, v___x_2683_, v___x_2682_);
return v___x_2686_;
}
}
static lean_object* _init_l_Lean_Parser_charLit___closed__1(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = l_Lean_Parser_charLitNoAntiquot;
v___x_2688_ = lean_obj_once(&l_Lean_Parser_charLit___closed__0, &l_Lean_Parser_charLit___closed__0_once, _init_l_Lean_Parser_charLit___closed__0);
v___x_2689_ = l_Lean_Parser_withAntiquot(v___x_2688_, v___x_2687_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_Parser_charLit(void){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_obj_once(&l_Lean_Parser_charLit___closed__1, &l_Lean_Parser_charLit___closed__1_once, _init_l_Lean_Parser_charLit___closed__1);
return v___x_2690_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1(){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__1));
v___x_2699_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___closed__2));
v___x_2700_ = l_Lean_addBuiltinDocString(v___x_2698_, v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2701_;
v_res_2701_ = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
stack->m_obj
 = v_res_2701_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1___boxed(lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
return v_res_2703_;
}
}
lean_object* l_Lean_Parser_nameLit_formatter(lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__2));
v___x_2720_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___boxed), 5, 0);
v___x_2721_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2719_, v___x_2720_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2721_;
}
}
LEAN_EXPORT void l_Lean_Parser_nameLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2714_ = stack[0].m_obj;
lean_object* v_a_2715_ = stack[1].m_obj;
lean_object* v_a_2716_ = stack[2].m_obj;
lean_object* v_a_2717_ = stack[3].m_obj;
lean_object* v_res_2722_;
v_res_2722_ = l_Lean_Parser_nameLit_formatter(v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
stack->m_obj
 = v_res_2722_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter___boxed(lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Parser_nameLit_formatter(v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
return v_res_2728_;
}
}
lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v___f_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___f_2741_ = ((lean_object*)(l_Lean_Parser_rawIdent_parenthesizer___closed__0));
v___x_2742_ = ((lean_object*)(l_Lean_Parser_nameLit_parenthesizer___closed__0));
v___x_2743_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2742_, v___f_2741_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
return v___x_2743_;
}
}
LEAN_EXPORT void l_Lean_Parser_nameLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2736_ = stack[0].m_obj;
lean_object* v_a_2737_ = stack[1].m_obj;
lean_object* v_a_2738_ = stack[2].m_obj;
lean_object* v_a_2739_ = stack[3].m_obj;
lean_object* v_res_2744_;
v_res_2744_ = l_Lean_Parser_nameLit_parenthesizer(v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
stack->m_obj
 = v_res_2744_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer___boxed(lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Parser_nameLit_parenthesizer(v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2750_;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__0(void){
_start:
{
uint8_t v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2751_ = 0;
v___x_2752_ = 1;
v___x_2753_ = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__1));
v___x_2754_ = ((lean_object*)(l_Lean_Parser_nameLit_formatter___closed__0));
v___x_2755_ = l_Lean_Parser_mkAntiquot(v___x_2754_, v___x_2753_, v___x_2752_, v___x_2751_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Parser_nameLit___closed__1(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_Parser_nameLitNoAntiquot;
v___x_2757_ = lean_obj_once(&l_Lean_Parser_nameLit___closed__0, &l_Lean_Parser_nameLit___closed__0_once, _init_l_Lean_Parser_nameLit___closed__0);
v___x_2758_ = l_Lean_Parser_withAntiquot(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_Parser_nameLit(void){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_obj_once(&l_Lean_Parser_nameLit___closed__1, &l_Lean_Parser_nameLit___closed__1_once, _init_l_Lean_Parser_nameLit___closed__1);
return v___x_2759_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1(){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__1));
v___x_2768_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___closed__2));
v___x_2769_ = l_Lean_addBuiltinDocString(v___x_2767_, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2770_;
v_res_2770_ = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
stack->m_obj
 = v_res_2770_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1___boxed(lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
return v_res_2772_;
}
}
lean_object* l_Lean_Parser_group_formatter(lean_object* v_p_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
v___x_2783_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_2782_, v_p_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2783_;
}
}
LEAN_EXPORT void l_Lean_Parser_group_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2776_ = stack[0].m_obj;
lean_object* v_a_2777_ = stack[1].m_obj;
lean_object* v_a_2778_ = stack[2].m_obj;
lean_object* v_a_2779_ = stack[3].m_obj;
lean_object* v_a_2780_ = stack[4].m_obj;
lean_object* v_res_2784_;
v_res_2784_ = l_Lean_Parser_group_formatter(v_p_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
stack->m_obj
 = v_res_2784_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter___boxed(lean_object* v_p_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Parser_group_formatter(v_p_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
return v_res_2791_;
}
}
lean_object* l_Lean_Parser_group_parenthesizer(lean_object* v_p_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
v___x_2799_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_2798_, v_p_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
return v___x_2799_;
}
}
LEAN_EXPORT void l_Lean_Parser_group_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2792_ = stack[0].m_obj;
lean_object* v_a_2793_ = stack[1].m_obj;
lean_object* v_a_2794_ = stack[2].m_obj;
lean_object* v_a_2795_ = stack[3].m_obj;
lean_object* v_a_2796_ = stack[4].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l_Lean_Parser_group_parenthesizer(v_p_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer___boxed(lean_object* v_p_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Parser_group_parenthesizer(v_p_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group(lean_object* v_p_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
v___x_2810_ = l_Lean_Parser_node(v___x_2809_, v_p_2808_);
return v___x_2810_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1(){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0));
v___x_2818_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__1));
v___x_2819_ = l_Lean_addBuiltinDocString(v___x_2817_, v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2820_;
v_res_2820_ = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
stack->m_obj
 = v_res_2820_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___boxed(lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
return v_res_2822_;
}
}
lean_object* l_Lean_Parser_many1Indent_formatter(lean_object* v_p_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
v___x_2830_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2830_, 0, v___x_2829_);
lean_closure_set(v___x_2830_, 1, v_p_2823_);
v___x_2831_ = l_Lean_Parser_many1_formatter(v___x_2830_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
return v___x_2831_;
}
}
LEAN_EXPORT void l_Lean_Parser_many1Indent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2823_ = stack[0].m_obj;
lean_object* v_a_2824_ = stack[1].m_obj;
lean_object* v_a_2825_ = stack[2].m_obj;
lean_object* v_a_2826_ = stack[3].m_obj;
lean_object* v_a_2827_ = stack[4].m_obj;
lean_object* v_res_2832_;
v_res_2832_ = l_Lean_Parser_many1Indent_formatter(v_p_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
stack->m_obj
 = v_res_2832_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object* v_p_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Parser_many1Indent_formatter(v_p_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
return v_res_2839_;
}
}
lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object* v_p_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2846_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_2847_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2847_, 0, v___x_2846_);
lean_closure_set(v___x_2847_, 1, v_p_2840_);
v___x_2848_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2848_, 0, v___x_2847_);
v___x_2849_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(v___x_2848_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2849_;
}
}
LEAN_EXPORT void l_Lean_Parser_many1Indent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2840_ = stack[0].m_obj;
lean_object* v_a_2841_ = stack[1].m_obj;
lean_object* v_a_2842_ = stack[2].m_obj;
lean_object* v_a_2843_ = stack[3].m_obj;
lean_object* v_a_2844_ = stack[4].m_obj;
lean_object* v_res_2850_;
v_res_2850_ = l_Lean_Parser_many1Indent_parenthesizer(v_p_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
stack->m_obj
 = v_res_2850_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object* v_p_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Parser_many1Indent_parenthesizer(v_p_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2857_;
}
}
static lean_object* _init_l_Lean_Parser_many1Indent___closed__1(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_Lean_Parser_many1Indent___closed__0));
v___x_2860_ = l_Lean_Parser_checkColGe(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent(lean_object* v_p_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = lean_obj_once(&l_Lean_Parser_many1Indent___closed__1, &l_Lean_Parser_many1Indent___closed__1_once, _init_l_Lean_Parser_many1Indent___closed__1);
v___x_2863_ = l_Lean_Parser_andthen(v___x_2862_, v_p_2861_);
v___x_2864_ = l_Lean_Parser_many1(v___x_2863_);
v___x_2865_ = l_Lean_Parser_withPosition(v___x_2864_);
return v___x_2865_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1(){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__1));
v___x_2874_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___closed__2));
v___x_2875_ = l_Lean_addBuiltinDocString(v___x_2873_, v___x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2876_;
v_res_2876_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
stack->m_obj
 = v_res_2876_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1___boxed(lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
return v_res_2878_;
}
}
lean_object* l_Lean_Parser_manyIndent_formatter(lean_object* v_p_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
v___x_2886_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2886_, 0, v___x_2885_);
lean_closure_set(v___x_2886_, 1, v_p_2879_);
v___x_2887_ = l_Lean_Parser_many_formatter(v___x_2886_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
return v___x_2887_;
}
}
LEAN_EXPORT void l_Lean_Parser_manyIndent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2879_ = stack[0].m_obj;
lean_object* v_a_2880_ = stack[1].m_obj;
lean_object* v_a_2881_ = stack[2].m_obj;
lean_object* v_a_2882_ = stack[3].m_obj;
lean_object* v_a_2883_ = stack[4].m_obj;
lean_object* v_res_2888_;
v_res_2888_ = l_Lean_Parser_manyIndent_formatter(v_p_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
stack->m_obj
 = v_res_2888_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter___boxed(lean_object* v_p_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Parser_manyIndent_formatter(v_p_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
return v_res_2895_;
}
}
lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object* v_p_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2902_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_2903_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2903_, 0, v___x_2902_);
lean_closure_set(v___x_2903_, 1, v_p_2896_);
v___x_2904_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2904_, 0, v___x_2903_);
v___x_2905_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(v___x_2904_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
return v___x_2905_;
}
}
LEAN_EXPORT void l_Lean_Parser_manyIndent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2896_ = stack[0].m_obj;
lean_object* v_a_2897_ = stack[1].m_obj;
lean_object* v_a_2898_ = stack[2].m_obj;
lean_object* v_a_2899_ = stack[3].m_obj;
lean_object* v_a_2900_ = stack[4].m_obj;
lean_object* v_res_2906_;
v_res_2906_ = l_Lean_Parser_manyIndent_parenthesizer(v_p_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
stack->m_obj
 = v_res_2906_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer___boxed(lean_object* v_p_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Parser_manyIndent_parenthesizer(v_p_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent(lean_object* v_p_2914_){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2915_ = lean_obj_once(&l_Lean_Parser_many1Indent___closed__1, &l_Lean_Parser_many1Indent___closed__1_once, _init_l_Lean_Parser_many1Indent___closed__1);
v___x_2916_ = l_Lean_Parser_andthen(v___x_2915_, v_p_2914_);
v___x_2917_ = l_Lean_Parser_many(v___x_2916_);
v___x_2918_ = l_Lean_Parser_withPosition(v___x_2917_);
return v___x_2918_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1(){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__1));
v___x_2927_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___closed__2));
v___x_2928_ = l_Lean_addBuiltinDocString(v___x_2926_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2929_;
v_res_2929_ = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
stack->m_obj
 = v_res_2929_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1___boxed(lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
return v_res_2931_;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__0(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l_Lean_Parser_many1Indent___closed__0));
v___x_2933_ = l_Lean_Parser_checkColEq(v___x_2932_);
return v___x_2933_;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__2(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l_Lean_Parser_sepByIndent___closed__1));
v___x_2936_ = l_Lean_Parser_checkLinebreakBefore(v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__3(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = l_Lean_Parser_pushNone;
v___x_2938_ = lean_obj_once(&l_Lean_Parser_sepByIndent___closed__2, &l_Lean_Parser_sepByIndent___closed__2_once, _init_l_Lean_Parser_sepByIndent___closed__2);
v___x_2939_ = l_Lean_Parser_andthen(v___x_2938_, v___x_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent___closed__4(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_obj_once(&l_Lean_Parser_sepByIndent___closed__3, &l_Lean_Parser_sepByIndent___closed__3_once, _init_l_Lean_Parser_sepByIndent___closed__3);
v___x_2941_ = lean_obj_once(&l_Lean_Parser_sepByIndent___closed__0, &l_Lean_Parser_sepByIndent___closed__0_once, _init_l_Lean_Parser_sepByIndent___closed__0);
v___x_2942_ = l_Lean_Parser_andthen(v___x_2941_, v___x_2940_);
return v___x_2942_;
}
}
lean_object* l_Lean_Parser_sepByIndent(lean_object* v_p_2943_, lean_object* v_sep_2944_, lean_object* v_psep_2945_, uint8_t v_allowTrailingSep_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_p_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2947_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
v___x_2948_ = lean_obj_once(&l_Lean_Parser_many___closed__0, &l_Lean_Parser_many___closed__0_once, _init_l_Lean_Parser_many___closed__0);
v_p_2949_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_2947_, v_p_2943_, v___x_2948_);
v___x_2950_ = lean_obj_once(&l_Lean_Parser_many1Indent___closed__1, &l_Lean_Parser_many1Indent___closed__1_once, _init_l_Lean_Parser_many1Indent___closed__1);
v___x_2951_ = l_Lean_Parser_andthen(v___x_2950_, v_p_2949_);
v___x_2952_ = lean_obj_once(&l_Lean_Parser_sepByIndent___closed__4, &l_Lean_Parser_sepByIndent___closed__4_once, _init_l_Lean_Parser_sepByIndent___closed__4);
v___x_2953_ = l_Lean_Parser_orelse(v_psep_2945_, v___x_2952_);
v___x_2954_ = l_Lean_Parser_sepBy(v___x_2951_, v_sep_2944_, v___x_2953_, v_allowTrailingSep_2946_);
v___x_2955_ = l_Lean_Parser_withPosition(v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepByIndent_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2943_ = stack[0].m_obj;
lean_object* v_sep_2944_ = stack[1].m_obj;
lean_object* v_psep_2945_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_2946_ = stack[3].m_num;
lean_object* v_res_2956_;
v_res_2956_ = l_Lean_Parser_sepByIndent(v_p_2943_, v_sep_2944_, v_psep_2945_, v_allowTrailingSep_2946_);
stack->m_obj
 = v_res_2956_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent___boxed(lean_object* v_p_2957_, lean_object* v_sep_2958_, lean_object* v_psep_2959_, lean_object* v_allowTrailingSep_2960_){
_start:
{
uint8_t v_allowTrailingSep_boxed_2961_; lean_object* v_res_2962_; 
v_allowTrailingSep_boxed_2961_ = lean_unbox(v_allowTrailingSep_2960_);
v_res_2962_ = l_Lean_Parser_sepByIndent(v_p_2957_, v_sep_2958_, v_psep_2959_, v_allowTrailingSep_boxed_2961_);
return v_res_2962_;
}
}
lean_object* l_Lean_Parser_sepBy1Indent(lean_object* v_p_2963_, lean_object* v_sep_2964_, lean_object* v_psep_2965_, uint8_t v_allowTrailingSep_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_p_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2967_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
v___x_2968_ = lean_obj_once(&l_Lean_Parser_many___closed__0, &l_Lean_Parser_many___closed__0_once, _init_l_Lean_Parser_many___closed__0);
v_p_2969_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_2967_, v_p_2963_, v___x_2968_);
v___x_2970_ = lean_obj_once(&l_Lean_Parser_many1Indent___closed__1, &l_Lean_Parser_many1Indent___closed__1_once, _init_l_Lean_Parser_many1Indent___closed__1);
v___x_2971_ = l_Lean_Parser_andthen(v___x_2970_, v_p_2969_);
v___x_2972_ = lean_obj_once(&l_Lean_Parser_sepByIndent___closed__4, &l_Lean_Parser_sepByIndent___closed__4_once, _init_l_Lean_Parser_sepByIndent___closed__4);
v___x_2973_ = l_Lean_Parser_orelse(v_psep_2965_, v___x_2972_);
v___x_2974_ = l_Lean_Parser_sepBy1(v___x_2971_, v_sep_2964_, v___x_2973_, v_allowTrailingSep_2966_);
v___x_2975_ = l_Lean_Parser_withPosition(v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1Indent_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2963_ = stack[0].m_obj;
lean_object* v_sep_2964_ = stack[1].m_obj;
lean_object* v_psep_2965_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_2966_ = stack[3].m_num;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_Parser_sepBy1Indent(v_p_2963_, v_sep_2964_, v_psep_2965_, v_allowTrailingSep_2966_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent___boxed(lean_object* v_p_2977_, lean_object* v_sep_2978_, lean_object* v_psep_2979_, lean_object* v_allowTrailingSep_2980_){
_start:
{
uint8_t v_allowTrailingSep_boxed_2981_; lean_object* v_res_2982_; 
v_allowTrailingSep_boxed_2981_ = lean_unbox(v_allowTrailingSep_2980_);
v_res_2982_ = l_Lean_Parser_sepBy1Indent(v_p_2977_, v_sep_2978_, v_psep_2979_, v_allowTrailingSep_boxed_2981_);
return v_res_2982_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v_stxTrav_2986_; lean_object* v_cur_2987_; lean_object* v___x_2988_; 
v___x_2985_ = lean_st_ref_get(v___y_2983_);
v_stxTrav_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_ref(v_stxTrav_2986_);
lean_dec(v___x_2985_);
v_cur_2987_ = lean_ctor_get(v_stxTrav_2986_, 0);
lean_inc(v_cur_2987_);
lean_dec_ref(v_stxTrav_2986_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_cur_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2983_ = stack[0].m_obj;
lean_object* v_res_2989_;
v_res_2989_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v___y_2983_);
stack->m_obj
 = v_res_2989_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v___y_2990_);
lean_dec(v___y_2990_);
return v_res_2992_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v___y_2994_);
return v___x_2998_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2993_ = stack[0].m_obj;
lean_object* v___y_2994_ = stack[1].m_obj;
lean_object* v___y_2995_ = stack[2].m_obj;
lean_object* v___y_2996_ = stack[3].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___boxed(lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0(v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3005_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; lean_object* v_stxTrav_3009_; lean_object* v_leadWord_3010_; uint8_t v_leadWordIdent_3011_; uint8_t v_isUngrouped_3012_; uint8_t v_mustBeGrouped_3013_; lean_object* v_stack_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3025_; 
v___x_3008_ = lean_st_ref_take(v___y_3006_);
v_stxTrav_3009_ = lean_ctor_get(v___x_3008_, 0);
v_leadWord_3010_ = lean_ctor_get(v___x_3008_, 1);
v_leadWordIdent_3011_ = lean_ctor_get_uint8(v___x_3008_, sizeof(void*)*3);
v_isUngrouped_3012_ = lean_ctor_get_uint8(v___x_3008_, sizeof(void*)*3 + 1);
v_mustBeGrouped_3013_ = lean_ctor_get_uint8(v___x_3008_, sizeof(void*)*3 + 2);
v_stack_3014_ = lean_ctor_get(v___x_3008_, 2);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3016_ = v___x_3008_;
v_isShared_3017_ = v_isSharedCheck_3025_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_stack_3014_);
lean_inc(v_leadWord_3010_);
lean_inc(v_stxTrav_3009_);
lean_dec(v___x_3008_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3025_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3018_ = lean_box(0);
v___x_3019_ = l_Lean_Syntax_Traverser_left(v_stxTrav_3009_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3019_);
v___x_3021_ = v___x_3016_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_leadWord_3010_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_stack_3014_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*3, v_leadWordIdent_3011_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*3 + 1, v_isUngrouped_3012_);
lean_ctor_set_uint8(v_reuseFailAlloc_3024_, sizeof(void*)*3 + 2, v_mustBeGrouped_3013_);
v___x_3021_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_st_ref_put(v___y_3006_, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3018_);
return v___x_3023_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3006_ = stack[0].m_obj;
lean_object* v_res_3026_;
v_res_3026_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_3006_);
stack->m_obj
 = v_res_3026_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg___boxed(lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_3027_);
lean_dec(v___y_3027_);
return v_res_3029_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_3031_);
return v___x_3035_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3030_ = stack[0].m_obj;
lean_object* v___y_3031_ = stack[1].m_obj;
lean_object* v___y_3032_ = stack[2].m_obj;
lean_object* v___y_3033_ = stack[3].m_obj;
lean_object* v_res_3036_;
v_res_3036_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___boxed(lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2(v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
return v_res_3042_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(lean_object* v_pSep_3046_, lean_object* v___x_3047_, lean_object* v_p_3048_, lean_object* v_as_x27_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
if (lean_obj_tag(v_as_x27_3049_) == 0)
{
lean_object* v___x_3056_; 
lean_dec_ref(v_p_3048_);
lean_dec_ref(v_pSep_3046_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_b_3050_);
return v___x_3056_;
}
else
{
lean_object* v_head_3057_; lean_object* v_tail_3058_; lean_object* v___x_3059_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_head_3057_ = lean_ctor_get(v_as_x27_3049_, 0);
v_tail_3058_ = lean_ctor_get(v_as_x27_3049_, 1);
v___x_3059_ = lean_box(0);
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_unsigned_to_nat(2u);
v___x_3065_ = lean_nat_mod(v_head_3057_, v___x_3064_);
v___x_3066_ = lean_nat_dec_eq(v___x_3065_, v___x_3063_);
lean_dec(v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = lean_st_ref_get(v___y_3052_);
v___x_3068_ = l_Lean_PrettyPrinter_backtrackExceptionId;
lean_inc_ref(v_pSep_3046_);
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3069_ = lean_apply_5(v_pSep_3046_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, lean_box(0));
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref_known(v___x_3069_, 1);
lean_dec(v___x_3067_);
v_as_x27_3049_ = v_tail_3058_;
v_b_3050_ = v___x_3059_;
goto _start;
}
else
{
lean_object* v_a_3071_; uint8_t v___y_3073_; uint8_t v___x_3082_; 
v_a_3071_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3071_);
v___x_3082_ = l_Lean_Exception_isInterrupt(v_a_3071_);
if (v___x_3082_ == 0)
{
uint8_t v___x_3083_; 
lean_inc(v_a_3071_);
v___x_3083_ = l_Lean_Exception_isRuntime(v_a_3071_);
v___y_3073_ = v___x_3083_;
goto v___jp_3072_;
}
else
{
v___y_3073_ = v___x_3082_;
goto v___jp_3072_;
}
v___jp_3072_:
{
if (v___y_3073_ == 0)
{
if (lean_obj_tag(v_a_3071_) == 0)
{
lean_dec_ref_known(v_a_3071_, 2);
lean_dec(v___x_3067_);
lean_dec_ref(v_p_3048_);
lean_dec_ref(v_pSep_3046_);
return v___x_3069_;
}
else
{
lean_object* v_id_3074_; uint8_t v___x_3075_; 
v_id_3074_ = lean_ctor_get(v_a_3071_, 0);
lean_inc(v_id_3074_);
lean_dec_ref_known(v_a_3071_, 2);
v___x_3075_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3068_, v_id_3074_);
lean_dec(v_id_3074_);
if (v___x_3075_ == 0)
{
lean_dec(v___x_3067_);
lean_dec_ref(v_p_3048_);
lean_dec_ref(v_pSep_3046_);
return v___x_3069_;
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
lean_dec_ref_known(v___x_3069_, 1);
v___x_3076_ = lean_st_ref_swap(v___y_3052_, v___x_3067_);
lean_dec(v___x_3076_);
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3078_ = lean_nat_sub(v___x_3047_, v___x_3077_);
v___x_3079_ = lean_nat_dec_eq(v_head_3057_, v___x_3078_);
lean_dec(v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1));
v___x_3081_ = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(v___x_3080_, v___y_3052_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_dec_ref_known(v___x_3081_, 1);
goto v___jp_3060_;
}
else
{
lean_dec_ref(v_p_3048_);
lean_dec_ref(v_pSep_3046_);
return v___x_3081_;
}
}
else
{
goto v___jp_3060_;
}
}
}
}
else
{
lean_dec(v_a_3071_);
lean_dec(v___x_3067_);
lean_dec_ref(v_p_3048_);
lean_dec_ref(v_pSep_3046_);
return v___x_3069_;
}
}
}
}
else
{
lean_object* v___x_3084_; 
lean_inc_ref(v_p_3048_);
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3084_ = lean_apply_5(v_p_3048_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, lean_box(0));
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref_known(v___x_3084_, 1);
v_as_x27_3049_ = v_tail_3058_;
v_b_3050_ = v___x_3059_;
goto _start;
}
else
{
lean_dec_ref(v_p_3048_);
lean_dec_ref(v_pSep_3046_);
return v___x_3084_;
}
}
v___jp_3060_:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Parser_sepByIndent_formatter_spec__2___redArg(v___y_3052_);
lean_dec_ref(v___x_3061_);
v_as_x27_3049_ = v_tail_3058_;
v_b_3050_ = v___x_3059_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pSep_3046_ = stack[0].m_obj;
lean_object* v___x_3047_ = stack[1].m_obj;
lean_object* v_p_3048_ = stack[2].m_obj;
lean_object* v_as_x27_3049_ = stack[3].m_obj;
lean_object* v_b_3050_ = stack[4].m_obj;
lean_object* v___y_3051_ = stack[5].m_obj;
lean_object* v___y_3052_ = stack[6].m_obj;
lean_object* v___y_3053_ = stack[7].m_obj;
lean_object* v___y_3054_ = stack[8].m_obj;
lean_object* v_res_3086_;
v_res_3086_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(v_pSep_3046_, v___x_3047_, v_p_3048_, v_as_x27_3049_, v_b_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
stack->m_obj
 = v_res_3086_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___boxed(lean_object* v_pSep_3087_, lean_object* v___x_3088_, lean_object* v_p_3089_, lean_object* v_as_x27_3090_, lean_object* v_b_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(v_pSep_3087_, v___x_3088_, v_p_3089_, v_as_x27_3090_, v_b_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v_as_x27_3090_);
lean_dec(v___x_3088_);
return v_res_3097_;
}
}
lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(lean_object* v_pSep_3098_, lean_object* v___x_3099_, lean_object* v_p_3100_, lean_object* v___x_3101_, lean_object* v___x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(v_pSep_3098_, v___x_3099_, v_p_3100_, v___x_3101_, v___x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3108_, 0);
lean_dec(v_unused_3116_);
v___x_3110_ = v___x_3108_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_dec(v___x_3108_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3102_);
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3102_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
return v___x_3108_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_sepByIndent_formatter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pSep_3098_ = stack[0].m_obj;
lean_object* v___x_3099_ = stack[1].m_obj;
lean_object* v_p_3100_ = stack[2].m_obj;
lean_object* v___x_3101_ = stack[3].m_obj;
lean_object* v___x_3102_ = stack[4].m_obj;
lean_object* v___y_3103_ = stack[5].m_obj;
lean_object* v___y_3104_ = stack[6].m_obj;
lean_object* v___y_3105_ = stack[7].m_obj;
lean_object* v___y_3106_ = stack[8].m_obj;
lean_object* v_res_3117_;
v_res_3117_ = l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(v_pSep_3098_, v___x_3099_, v_p_3100_, v___x_3101_, v___x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
stack->m_obj
 = v_res_3117_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(lean_object* v_pSep_3118_, lean_object* v___x_3119_, lean_object* v_p_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(v_pSep_3118_, v___x_3119_, v_p_3120_, v___x_3121_, v___x_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___x_3121_);
lean_dec(v___x_3119_);
return v_res_3128_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(lean_object* v_as_3129_, size_t v_i_3130_, size_t v_stop_3131_){
_start:
{
uint8_t v___x_3132_; 
v___x_3132_ = lean_usize_dec_eq(v_i_3130_, v_stop_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3133_ = lean_array_uget_borrowed(v_as_3129_, v_i_3130_);
v___x_3134_ = lean_unbox(v___x_3133_);
if (v___x_3134_ == 0)
{
size_t v___x_3135_; size_t v___x_3136_; 
v___x_3135_ = ((size_t)1ULL);
v___x_3136_ = lean_usize_add(v_i_3130_, v___x_3135_);
v_i_3130_ = v___x_3136_;
goto _start;
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_unbox(v___x_3133_);
return v___x_3138_;
}
}
else
{
uint8_t v___x_3139_; 
v___x_3139_ = 0;
return v___x_3139_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3129_ = stack[0].m_obj;
size_t v_i_3130_ = stack[1].m_num;
size_t v_stop_3131_ = stack[2].m_num;
uint8_t v_res_3140_;
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(v_as_3129_, v_i_3130_, v_stop_3131_);
stack->m_num = v_res_3140_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4___boxed(lean_object* v_as_3141_, lean_object* v_i_3142_, lean_object* v_stop_3143_){
_start:
{
size_t v_i_boxed_3144_; size_t v_stop_boxed_3145_; uint8_t v_res_3146_; lean_object* v_r_3147_; 
v_i_boxed_3144_ = lean_unbox_usize(v_i_3142_);
lean_dec(v_i_3142_);
v_stop_boxed_3145_ = lean_unbox_usize(v_stop_3143_);
lean_dec(v_stop_3143_);
v_res_3146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(v_as_3141_, v_i_boxed_3144_, v_stop_boxed_3145_);
lean_dec_ref(v_as_3141_);
v_r_3147_ = lean_box(v_res_3146_);
return v_r_3147_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(lean_object* v_a_3148_, size_t v_sz_3149_, size_t v_i_3150_, lean_object* v_bs_3151_){
_start:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_usize_dec_lt(v_i_3150_, v_sz_3149_);
if (v___x_3152_ == 0)
{
return v_bs_3151_;
}
else
{
lean_object* v_v_3153_; lean_object* v___x_3154_; lean_object* v_bs_x27_3155_; uint8_t v___y_3157_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_v_3153_ = lean_array_uget(v_bs_3151_, v_i_3150_);
v___x_3154_ = lean_unsigned_to_nat(0u);
v_bs_x27_3155_ = lean_array_uset(v_bs_3151_, v_i_3150_, v___x_3154_);
v___x_3163_ = lean_usize_to_nat(v_i_3150_);
v___x_3164_ = lean_unsigned_to_nat(2u);
v___x_3165_ = lean_nat_mod(v___x_3163_, v___x_3164_);
v___x_3166_ = lean_unsigned_to_nat(1u);
v___x_3167_ = lean_nat_dec_eq(v___x_3165_, v___x_3166_);
lean_dec(v___x_3165_);
if (v___x_3167_ == 0)
{
lean_dec(v___x_3163_);
lean_dec(v_v_3153_);
v___y_3157_ = v___x_3167_;
goto v___jp_3156_;
}
else
{
uint8_t v___x_3168_; 
v___x_3168_ = l_Lean_Syntax_matchesNull(v_v_3153_, v___x_3154_);
if (v___x_3168_ == 0)
{
lean_dec(v___x_3163_);
v___y_3157_ = v___x_3168_;
goto v___jp_3156_;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3169_ = l_Lean_Syntax_getArgs(v_a_3148_);
v___x_3170_ = lean_array_get_size(v___x_3169_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = lean_nat_sub(v___x_3170_, v___x_3166_);
v___x_3172_ = lean_nat_dec_eq(v___x_3163_, v___x_3171_);
lean_dec(v___x_3171_);
lean_dec(v___x_3163_);
if (v___x_3172_ == 0)
{
v___y_3157_ = v___x_3168_;
goto v___jp_3156_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = 0;
v___y_3157_ = v___x_3173_;
goto v___jp_3156_;
}
}
}
v___jp_3156_:
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3150_, v___x_3158_);
v___x_3160_ = lean_box(v___y_3157_);
v___x_3161_ = lean_array_uset(v_bs_x27_3155_, v_i_3150_, v___x_3160_);
v_i_3150_ = v___x_3159_;
v_bs_3151_ = v___x_3161_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3148_ = stack[0].m_obj;
size_t v_sz_3149_ = stack[1].m_num;
size_t v_i_3150_ = stack[2].m_num;
lean_object* v_bs_3151_ = stack[3].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(v_a_3148_, v_sz_3149_, v_i_3150_, v_bs_3151_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(lean_object* v_a_3175_, lean_object* v_sz_3176_, lean_object* v_i_3177_, lean_object* v_bs_3178_){
_start:
{
size_t v_sz_boxed_3179_; size_t v_i_boxed_3180_; lean_object* v_res_3181_; 
v_sz_boxed_3179_ = lean_unbox_usize(v_sz_3176_);
lean_dec(v_sz_3176_);
v_i_boxed_3180_ = lean_unbox_usize(v_i_3177_);
lean_dec(v_i_3177_);
v_res_3181_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(v_a_3175_, v_sz_boxed_3179_, v_i_boxed_3180_, v_bs_3178_);
lean_dec(v_a_3175_);
return v_res_3181_;
}
}
lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object* v_p_3182_, lean_object* v_pSep_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3189_; lean_object* v_a_3190_; lean_object* v___x_3191_; uint8_t v___y_3193_; size_t v_sz_3209_; size_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3189_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_sepByIndent_formatter_spec__0___redArg(v_a_3185_);
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref(v___x_3189_);
v___x_3191_ = l_Lean_Syntax_getArgs(v_a_3190_);
v_sz_3209_ = lean_array_size(v___x_3191_);
v___x_3210_ = ((size_t)0ULL);
lean_inc_ref(v___x_3191_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(v_a_3190_, v_sz_3209_, v___x_3210_, v___x_3191_);
lean_dec(v_a_3190_);
v___x_3212_ = lean_unsigned_to_nat(0u);
v___x_3213_ = lean_array_get_size(v___x_3211_);
v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_dec_ref(v___x_3211_);
v___y_3193_ = v___x_3214_;
goto v___jp_3192_;
}
else
{
if (v___x_3214_ == 0)
{
lean_dec_ref(v___x_3211_);
v___y_3193_ = v___x_3214_;
goto v___jp_3192_;
}
else
{
size_t v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = lean_usize_of_nat(v___x_3213_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Parser_sepByIndent_formatter_spec__4(v___x_3211_, v___x_3210_, v___x_3215_);
lean_dec_ref(v___x_3211_);
v___y_3193_ = v___x_3216_;
goto v___jp_3192_;
}
}
v___jp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___f_3198_; lean_object* v___x_3199_; 
v___x_3194_ = lean_array_get_size(v___x_3191_);
lean_dec_ref(v___x_3191_);
v___x_3195_ = l_List_range(v___x_3194_);
v___x_3196_ = l_List_reverse___redArg(v___x_3195_);
v___x_3197_ = lean_box(0);
v___f_3198_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3198_, 0, v_pSep_3183_);
lean_closure_set(v___f_3198_, 1, v___x_3194_);
lean_closure_set(v___f_3198_, 2, v_p_3182_);
lean_closure_set(v___f_3198_, 3, v___x_3196_);
lean_closure_set(v___f_3198_, 4, v___x_3197_);
v___x_3199_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___f_3198_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3208_);
v___x_3201_ = v___x_3199_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_dec(v___x_3199_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
if (v___y_3193_ == 0)
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3197_);
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3197_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
else
{
lean_object* v___x_3206_; 
lean_del_object(v___x_3201_);
v___x_3206_ = l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(v___y_3193_, v_a_3185_);
return v___x_3206_;
}
}
}
else
{
return v___x_3199_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_sepByIndent_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3182_ = stack[0].m_obj;
lean_object* v_pSep_3183_ = stack[1].m_obj;
lean_object* v_a_3184_ = stack[2].m_obj;
lean_object* v_a_3185_ = stack[3].m_obj;
lean_object* v_a_3186_ = stack[4].m_obj;
lean_object* v_a_3187_ = stack[5].m_obj;
lean_object* v_res_3217_;
v_res_3217_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_3182_, v_pSep_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
stack->m_obj
 = v_res_3217_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___boxed(lean_object* v_p_3218_, lean_object* v_pSep_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_3218_, v_pSep_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
return v_res_3225_;
}
}
lean_object* l_Lean_Parser_sepByIndent_formatter(lean_object* v_p_3226_, lean_object* v___sep_3227_, lean_object* v_pSep_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_3226_, v_pSep_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepByIndent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3226_ = stack[0].m_obj;
lean_object* v___sep_3227_ = stack[1].m_obj;
lean_object* v_pSep_3228_ = stack[2].m_obj;
lean_object* v_a_3229_ = stack[3].m_obj;
lean_object* v_a_3230_ = stack[4].m_obj;
lean_object* v_a_3231_ = stack[5].m_obj;
lean_object* v_a_3232_ = stack[6].m_obj;
lean_object* v_res_3235_;
v_res_3235_ = l_Lean_Parser_sepByIndent_formatter(v_p_3226_, v___sep_3227_, v_pSep_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
stack->m_obj
 = v_res_3235_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object* v_p_3236_, lean_object* v___sep_3237_, lean_object* v_pSep_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Parser_sepByIndent_formatter(v_p_3236_, v___sep_3237_, v_pSep_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec_ref(v___sep_3237_);
return v_res_3244_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(lean_object* v_a_3245_, lean_object* v_as_3246_, size_t v_sz_3247_, size_t v_i_3248_, lean_object* v_bs_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___redArg(v_a_3245_, v_sz_3247_, v_i_3248_, v_bs_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3245_ = stack[0].m_obj;
lean_object* v_as_3246_ = stack[1].m_obj;
size_t v_sz_3247_ = stack[2].m_num;
size_t v_i_3248_ = stack[3].m_num;
lean_object* v_bs_3249_ = stack[4].m_obj;
lean_object* v_res_3251_;
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(v_a_3245_, v_as_3246_, v_sz_3247_, v_i_3248_, v_bs_3249_);
stack->m_obj
 = v_res_3251_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1___boxed(lean_object* v_a_3252_, lean_object* v_as_3253_, lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_bs_3256_){
_start:
{
size_t v_sz_boxed_3257_; size_t v_i_boxed_3258_; lean_object* v_res_3259_; 
v_sz_boxed_3257_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3258_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Parser_sepByIndent_formatter_spec__1(v_a_3252_, v_as_3253_, v_sz_boxed_3257_, v_i_boxed_3258_, v_bs_3256_);
lean_dec_ref(v_as_3253_);
lean_dec(v_a_3252_);
return v_res_3259_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(lean_object* v_pSep_3260_, lean_object* v___x_3261_, lean_object* v_p_3262_, lean_object* v_as_3263_, lean_object* v_as_x27_3264_, lean_object* v_b_3265_, lean_object* v_a_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg(v_pSep_3260_, v___x_3261_, v_p_3262_, v_as_x27_3264_, v_b_3265_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pSep_3260_ = stack[0].m_obj;
lean_object* v___x_3261_ = stack[1].m_obj;
lean_object* v_p_3262_ = stack[2].m_obj;
lean_object* v_as_3263_ = stack[3].m_obj;
lean_object* v_as_x27_3264_ = stack[4].m_obj;
lean_object* v_b_3265_ = stack[5].m_obj;
lean_object* v___y_3267_ = stack[7].m_obj;
lean_object* v___y_3268_ = stack[8].m_obj;
lean_object* v___y_3269_ = stack[9].m_obj;
lean_object* v___y_3270_ = stack[10].m_obj;
lean_object* v_res_3273_;
v_res_3273_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(v_pSep_3260_, v___x_3261_, v_p_3262_, v_as_3263_, v_as_x27_3264_, v_b_3265_, lean_box(0), v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
stack->m_obj
 = v_res_3273_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___boxed(lean_object* v_pSep_3274_, lean_object* v___x_3275_, lean_object* v_p_3276_, lean_object* v_as_3277_, lean_object* v_as_x27_3278_, lean_object* v_b_3279_, lean_object* v_a_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3(v_pSep_3274_, v___x_3275_, v_p_3276_, v_as_3277_, v_as_x27_3278_, v_b_3279_, v_a_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v_as_x27_3278_);
lean_dec(v_as_3277_);
lean_dec(v___x_3275_);
return v_res_3286_;
}
}
lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg(lean_object* v_p_3287_, lean_object* v_pSep_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_3287_, v_pSep_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1Indent_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3287_ = stack[0].m_obj;
lean_object* v_pSep_3288_ = stack[1].m_obj;
lean_object* v_a_3289_ = stack[2].m_obj;
lean_object* v_a_3290_ = stack[3].m_obj;
lean_object* v_a_3291_ = stack[4].m_obj;
lean_object* v_a_3292_ = stack[5].m_obj;
lean_object* v_res_3295_;
v_res_3295_ = l_Lean_Parser_sepBy1Indent_formatter___redArg(v_p_3287_, v_pSep_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
stack->m_obj
 = v_res_3295_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg___boxed(lean_object* v_p_3296_, lean_object* v_pSep_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Parser_sepBy1Indent_formatter___redArg(v_p_3296_, v_pSep_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
return v_res_3303_;
}
}
lean_object* l_Lean_Parser_sepBy1Indent_formatter(lean_object* v_p_3304_, lean_object* v___sep_3305_, lean_object* v_pSep_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_3304_, v_pSep_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1Indent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3304_ = stack[0].m_obj;
lean_object* v___sep_3305_ = stack[1].m_obj;
lean_object* v_pSep_3306_ = stack[2].m_obj;
lean_object* v_a_3307_ = stack[3].m_obj;
lean_object* v_a_3308_ = stack[4].m_obj;
lean_object* v_a_3309_ = stack[5].m_obj;
lean_object* v_a_3310_ = stack[6].m_obj;
lean_object* v_res_3313_;
v_res_3313_ = l_Lean_Parser_sepBy1Indent_formatter(v_p_3304_, v___sep_3305_, v_pSep_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
stack->m_obj
 = v_res_3313_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___boxed(lean_object* v_p_3314_, lean_object* v___sep_3315_, lean_object* v_pSep_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Parser_sepBy1Indent_formatter(v_p_3314_, v___sep_3315_, v_pSep_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec_ref(v___sep_3315_);
return v_res_3322_;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__0(void){
_start:
{
lean_object* v___f_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___f_3323_ = ((lean_object*)(l_Lean_Parser_mkAntiquot_parenthesizer___closed__0));
v___x_3324_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
v___x_3325_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3325_, 0, v___x_3324_);
lean_closure_set(v___x_3325_, 1, v___f_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_obj_once(&l_Lean_Parser_sepByIndent_parenthesizer___closed__0, &l_Lean_Parser_sepByIndent_parenthesizer___closed__0_once, _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__0);
v___x_3327_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
v___x_3328_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3328_, 0, v___x_3327_);
lean_closure_set(v___x_3328_, 1, v___x_3326_);
return v___x_3328_;
}
}
lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object* v_p_3329_, lean_object* v_sep_3330_, lean_object* v_psep_3331_, uint8_t v_allowTrailingSep_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3338_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_3339_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
v___x_3340_ = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
v___x_3341_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3341_, 0, v___x_3339_);
lean_closure_set(v___x_3341_, 1, v_p_3329_);
lean_closure_set(v___x_3341_, 2, v___x_3340_);
v___x_3342_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3342_, 0, v___x_3338_);
lean_closure_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_obj_once(&l_Lean_Parser_sepByIndent_parenthesizer___closed__1, &l_Lean_Parser_sepByIndent_parenthesizer___closed__1_once, _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1);
v___x_3344_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3344_, 0, v_psep_3331_);
lean_closure_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_box(v_allowTrailingSep_3332_);
v___x_3346_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_3346_, 0, v___x_3342_);
lean_closure_set(v___x_3346_, 1, v_sep_3330_);
lean_closure_set(v___x_3346_, 2, v___x_3344_);
lean_closure_set(v___x_3346_, 3, v___x_3345_);
v___x_3347_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(v___x_3346_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
return v___x_3347_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepByIndent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3329_ = stack[0].m_obj;
lean_object* v_sep_3330_ = stack[1].m_obj;
lean_object* v_psep_3331_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_3332_ = stack[3].m_num;
lean_object* v_a_3333_ = stack[4].m_obj;
lean_object* v_a_3334_ = stack[5].m_obj;
lean_object* v_a_3335_ = stack[6].m_obj;
lean_object* v_a_3336_ = stack[7].m_obj;
lean_object* v_res_3348_;
v_res_3348_ = l_Lean_Parser_sepByIndent_parenthesizer(v_p_3329_, v_sep_3330_, v_psep_3331_, v_allowTrailingSep_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
stack->m_obj
 = v_res_3348_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object* v_p_3349_, lean_object* v_sep_3350_, lean_object* v_psep_3351_, lean_object* v_allowTrailingSep_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_allowTrailingSep_boxed_3358_; lean_object* v_res_3359_; 
v_allowTrailingSep_boxed_3358_ = lean_unbox(v_allowTrailingSep_3352_);
v_res_3359_ = l_Lean_Parser_sepByIndent_parenthesizer(v_p_3349_, v_sep_3350_, v_psep_3351_, v_allowTrailingSep_boxed_3358_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
return v_res_3359_;
}
}
lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object* v_p_3360_, lean_object* v_sep_3361_, lean_object* v_psep_3362_, uint8_t v_allowTrailingSep_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3369_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_3370_ = ((lean_object*)(l_Lean_Parser_sepByElemParser_formatter___closed__1));
v___x_3371_ = ((lean_object*)(l_Lean_Parser_many_parenthesizer___closed__0));
v___x_3372_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3372_, 0, v___x_3370_);
lean_closure_set(v___x_3372_, 1, v_p_3360_);
lean_closure_set(v___x_3372_, 2, v___x_3371_);
v___x_3373_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3373_, 0, v___x_3369_);
lean_closure_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_obj_once(&l_Lean_Parser_sepByIndent_parenthesizer___closed__1, &l_Lean_Parser_sepByIndent_parenthesizer___closed__1_once, _init_l_Lean_Parser_sepByIndent_parenthesizer___closed__1);
v___x_3375_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3375_, 0, v_psep_3362_);
lean_closure_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_box(v_allowTrailingSep_3363_);
v___x_3377_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_3377_, 0, v___x_3373_);
lean_closure_set(v___x_3377_, 1, v_sep_3361_);
lean_closure_set(v___x_3377_, 2, v___x_3375_);
lean_closure_set(v___x_3377_, 3, v___x_3376_);
v___x_3378_ = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(v___x_3377_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
return v___x_3378_;
}
}
LEAN_EXPORT void l_Lean_Parser_sepBy1Indent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3360_ = stack[0].m_obj;
lean_object* v_sep_3361_ = stack[1].m_obj;
lean_object* v_psep_3362_ = stack[2].m_obj;
uint8_t v_allowTrailingSep_3363_ = stack[3].m_num;
lean_object* v_a_3364_ = stack[4].m_obj;
lean_object* v_a_3365_ = stack[5].m_obj;
lean_object* v_a_3366_ = stack[6].m_obj;
lean_object* v_a_3367_ = stack[7].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l_Lean_Parser_sepBy1Indent_parenthesizer(v_p_3360_, v_sep_3361_, v_psep_3362_, v_allowTrailingSep_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(lean_object* v_p_3380_, lean_object* v_sep_3381_, lean_object* v_psep_3382_, lean_object* v_allowTrailingSep_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
uint8_t v_allowTrailingSep_boxed_3389_; lean_object* v_res_3390_; 
v_allowTrailingSep_boxed_3389_ = lean_unbox(v_allowTrailingSep_3383_);
v_res_3390_ = l_Lean_Parser_sepBy1Indent_parenthesizer(v_p_3380_, v_sep_3381_, v_psep_3382_, v_allowTrailingSep_boxed_3389_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
return v_res_3390_;
}
}
lean_object* l_Lean_Parser_notSymbol_formatter___redArg(){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
return v___x_3392_;
}
}
LEAN_EXPORT void l_Lean_Parser_notSymbol_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3393_;
v_res_3393_ = l_Lean_Parser_notSymbol_formatter___redArg();
stack->m_obj
 = v_res_3393_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg___boxed(lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Parser_notSymbol_formatter___redArg();
return v_res_3395_;
}
}
lean_object* l_Lean_Parser_notSymbol_formatter(lean_object* v_s_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg();
return v___x_3402_;
}
}
LEAN_EXPORT void l_Lean_Parser_notSymbol_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3396_ = stack[0].m_obj;
lean_object* v_a_3397_ = stack[1].m_obj;
lean_object* v_a_3398_ = stack[2].m_obj;
lean_object* v_a_3399_ = stack[3].m_obj;
lean_object* v_a_3400_ = stack[4].m_obj;
lean_object* v_res_3403_;
v_res_3403_ = l_Lean_Parser_notSymbol_formatter(v_s_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
stack->m_obj
 = v_res_3403_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object* v_s_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Parser_notSymbol_formatter(v_s_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec_ref(v_s_3404_);
return v_res_3410_;
}
}
lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg(){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
return v___x_3412_;
}
}
LEAN_EXPORT void l_Lean_Parser_notSymbol_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3413_;
v_res_3413_ = l_Lean_Parser_notSymbol_parenthesizer___redArg();
stack->m_obj
 = v_res_3413_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg___boxed(lean_object* v_a_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_Parser_notSymbol_parenthesizer___redArg();
return v_res_3415_;
}
}
lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object* v_s_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg();
return v___x_3422_;
}
}
LEAN_EXPORT void l_Lean_Parser_notSymbol_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3416_ = stack[0].m_obj;
lean_object* v_a_3417_ = stack[1].m_obj;
lean_object* v_a_3418_ = stack[2].m_obj;
lean_object* v_a_3419_ = stack[3].m_obj;
lean_object* v_a_3420_ = stack[4].m_obj;
lean_object* v_res_3423_;
v_res_3423_ = l_Lean_Parser_notSymbol_parenthesizer(v_s_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
stack->m_obj
 = v_res_3423_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object* v_s_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Parser_notSymbol_parenthesizer(v_s_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec_ref(v_s_3424_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol(lean_object* v_s_3431_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_inc_ref(v_s_3431_);
v___x_3432_ = l_Lean_Parser_symbol(v_s_3431_);
v___x_3433_ = l_Lean_Parser_notFollowedBy(v___x_3432_, v_s_3431_);
return v___x_3433_;
}
}
lean_object* l_Lean_Parser_patternIgnore_formatter(lean_object* v_p_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
v___x_3444_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_3443_, v_p_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
return v___x_3444_;
}
}
LEAN_EXPORT void l_Lean_Parser_patternIgnore_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3437_ = stack[0].m_obj;
lean_object* v_a_3438_ = stack[1].m_obj;
lean_object* v_a_3439_ = stack[2].m_obj;
lean_object* v_a_3440_ = stack[3].m_obj;
lean_object* v_a_3441_ = stack[4].m_obj;
lean_object* v_res_3445_;
v_res_3445_ = l_Lean_Parser_patternIgnore_formatter(v_p_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
stack->m_obj
 = v_res_3445_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter___boxed(lean_object* v_p_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Parser_patternIgnore_formatter(v_p_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
return v_res_3452_;
}
}
lean_object* l_Lean_Parser_patternIgnore_parenthesizer(lean_object* v_p_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
v___x_3460_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_3459_, v_p_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
return v___x_3460_;
}
}
LEAN_EXPORT void l_Lean_Parser_patternIgnore_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3453_ = stack[0].m_obj;
lean_object* v_a_3454_ = stack[1].m_obj;
lean_object* v_a_3455_ = stack[2].m_obj;
lean_object* v_a_3456_ = stack[3].m_obj;
lean_object* v_a_3457_ = stack[4].m_obj;
lean_object* v_res_3461_;
v_res_3461_ = l_Lean_Parser_patternIgnore_parenthesizer(v_p_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
stack->m_obj
 = v_res_3461_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer___boxed(lean_object* v_p_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Parser_patternIgnore_parenthesizer(v_p_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore(lean_object* v_p_3469_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
v___x_3471_ = l_Lean_Parser_node(v___x_3470_, v_p_3469_);
return v___x_3471_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1(){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0));
v___x_3479_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__1));
v___x_3480_ = l_Lean_addBuiltinDocString(v___x_3478_, v___x_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3481_;
v_res_3481_ = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
stack->m_obj
 = v_res_3481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___boxed(lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
return v_res_3483_;
}
}
static lean_object* _init_l_Lean_Parser_ppHardSpace(void){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Parser_skip;
return v___x_3484_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1(){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1));
v___x_3493_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__2));
v___x_3494_ = l_Lean_addBuiltinDocString(v___x_3492_, v___x_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3495_;
v_res_3495_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
stack->m_obj
 = v_res_3495_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___boxed(lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
return v_res_3497_;
}
}
static lean_object* _init_l_Lean_Parser_ppSpace(void){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Parser_skip;
return v___x_3498_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1(){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1));
v___x_3507_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__2));
v___x_3508_ = l_Lean_addBuiltinDocString(v___x_3506_, v___x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3509_;
v_res_3509_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
stack->m_obj
 = v_res_3509_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___boxed(lean_object* v_a_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
return v_res_3511_;
}
}
static lean_object* _init_l_Lean_Parser_ppLine(void){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_Parser_skip;
return v___x_3512_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1(){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1));
v___x_3521_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__2));
v___x_3522_ = l_Lean_addBuiltinDocString(v___x_3520_, v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3523_;
v_res_3523_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
stack->m_obj
 = v_res_3523_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___boxed(lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill(lean_object* v_a_3526_){
_start:
{
lean_inc_ref(v_a_3526_);
return v_a_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___boxed(lean_object* v_a_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Parser_ppRealFill(v_a_3527_);
lean_dec_ref(v_a_3527_);
return v_res_3528_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1(){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1));
v___x_3537_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__2));
v___x_3538_ = l_Lean_addBuiltinDocString(v___x_3536_, v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3539_;
v_res_3539_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
stack->m_obj
 = v_res_3539_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___boxed(lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup(lean_object* v_a_3542_){
_start:
{
lean_inc_ref(v_a_3542_);
return v_a_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___boxed(lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Parser_ppRealGroup(v_a_3543_);
lean_dec_ref(v_a_3543_);
return v_res_3544_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1(){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1));
v___x_3553_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__2));
v___x_3554_ = l_Lean_addBuiltinDocString(v___x_3552_, v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3555_;
v_res_3555_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
stack->m_obj
 = v_res_3555_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___boxed(lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent(lean_object* v_a_3558_){
_start:
{
lean_inc_ref(v_a_3558_);
return v_a_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___boxed(lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Parser_ppIndent(v_a_3559_);
lean_dec_ref(v_a_3559_);
return v_res_3560_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1(){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1));
v___x_3569_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__2));
v___x_3570_ = l_Lean_addBuiltinDocString(v___x_3568_, v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3571_;
v_res_3571_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
stack->m_obj
 = v_res_3571_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___boxed(lean_object* v_a_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup(lean_object* v_p_3574_){
_start:
{
lean_inc_ref(v_p_3574_);
return v_p_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___boxed(lean_object* v_p_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Parser_ppGroup(v_p_3575_);
lean_dec_ref(v_p_3575_);
return v_res_3576_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1(){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3584_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1));
v___x_3585_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__2));
v___x_3586_ = l_Lean_addBuiltinDocString(v___x_3584_, v___x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3587_;
v_res_3587_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
stack->m_obj
 = v_res_3587_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___boxed(lean_object* v_a_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent(lean_object* v_a_3590_){
_start:
{
lean_inc_ref(v_a_3590_);
return v_a_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___boxed(lean_object* v_a_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Parser_ppDedent(v_a_3591_);
lean_dec_ref(v_a_3591_);
return v_res_3592_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1(){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1));
v___x_3601_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__2));
v___x_3602_ = l_Lean_addBuiltinDocString(v___x_3600_, v___x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3603_;
v_res_3603_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
stack->m_obj
 = v_res_3603_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___boxed(lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
return v_res_3605_;
}
}
static lean_object* _init_l_Lean_Parser_ppAllowUngrouped(void){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_Parser_skip;
return v___x_3606_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1(){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1));
v___x_3615_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__2));
v___x_3616_ = l_Lean_addBuiltinDocString(v___x_3614_, v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3617_;
v_res_3617_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
stack->m_obj
 = v_res_3617_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___boxed(lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped(lean_object* v_a_3620_){
_start:
{
lean_inc_ref(v_a_3620_);
return v_a_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___boxed(lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Parser_ppDedentIfGrouped(v_a_3621_);
lean_dec_ref(v_a_3621_);
return v_res_3622_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1(){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1));
v___x_3631_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__2));
v___x_3632_ = l_Lean_addBuiltinDocString(v___x_3630_, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3633_;
v_res_3633_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
stack->m_obj
 = v_res_3633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___boxed(lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
return v_res_3635_;
}
}
static lean_object* _init_l_Lean_Parser_ppHardLineUnlessUngrouped(void){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Parser_skip;
return v___x_3636_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1(){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1));
v___x_3645_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__2));
v___x_3646_ = l_Lean_addBuiltinDocString(v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3647_;
v_res_3647_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
stack->m_obj
 = v_res_3647_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___boxed(lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
return v_res_3649_;
}
}
lean_object* l_Lean_ppHardSpace_formatter___redArg(lean_object* v_a_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l_Lean_ppHardSpace_formatter___redArg___closed__1));
v___x_3656_ = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(v___x_3655_, v_a_3653_);
return v___x_3656_;
}
}
LEAN_EXPORT void l_Lean_ppHardSpace_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3653_ = stack[0].m_obj;
lean_object* v_res_3657_;
v_res_3657_ = l_Lean_ppHardSpace_formatter___redArg(v_a_3653_);
stack->m_obj
 = v_res_3657_;
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg___boxed(lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_ppHardSpace_formatter___redArg(v_a_3658_);
lean_dec(v_a_3658_);
return v_res_3660_;
}
}
lean_object* l_Lean_ppHardSpace_formatter(lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_ppHardSpace_formatter___redArg(v_a_3662_);
return v___x_3666_;
}
}
LEAN_EXPORT void l_Lean_ppHardSpace_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3661_ = stack[0].m_obj;
lean_object* v_a_3662_ = stack[1].m_obj;
lean_object* v_a_3663_ = stack[2].m_obj;
lean_object* v_a_3664_ = stack[3].m_obj;
lean_object* v_res_3667_;
v_res_3667_ = l_Lean_ppHardSpace_formatter(v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
stack->m_obj
 = v_res_3667_;
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_ppHardSpace_formatter(v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
return v_res_3673_;
}
}
lean_object* l_Lean_ppSpace_formatter___redArg(lean_object* v_a_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v_a_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT void l_Lean_ppSpace_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3674_ = stack[0].m_obj;
lean_object* v_res_3677_;
v_res_3677_ = l_Lean_ppSpace_formatter___redArg(v_a_3674_);
stack->m_obj
 = v_res_3677_;
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg___boxed(lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_ppSpace_formatter___redArg(v_a_3678_);
lean_dec(v_a_3678_);
return v_res_3680_;
}
}
lean_object* l_Lean_ppSpace_formatter(lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v_a_3682_);
return v___x_3686_;
}
}
LEAN_EXPORT void l_Lean_ppSpace_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3681_ = stack[0].m_obj;
lean_object* v_a_3682_ = stack[1].m_obj;
lean_object* v_a_3683_ = stack[2].m_obj;
lean_object* v_a_3684_ = stack[3].m_obj;
lean_object* v_res_3687_;
v_res_3687_ = l_Lean_ppSpace_formatter(v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
stack->m_obj
 = v_res_3687_;
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___boxed(lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_ppSpace_formatter(v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
return v_res_3693_;
}
}
lean_object* l_Lean_ppLine_formatter___redArg(lean_object* v_a_3694_){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Parser_sepByIndent_formatter_spec__3___redArg___closed__1));
v___x_3697_ = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(v___x_3696_, v_a_3694_);
return v___x_3697_;
}
}
LEAN_EXPORT void l_Lean_ppLine_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3694_ = stack[0].m_obj;
lean_object* v_res_3698_;
v_res_3698_ = l_Lean_ppLine_formatter___redArg(v_a_3694_);
stack->m_obj
 = v_res_3698_;
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg___boxed(lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_ppLine_formatter___redArg(v_a_3699_);
lean_dec(v_a_3699_);
return v_res_3701_;
}
}
lean_object* l_Lean_ppLine_formatter(lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_ppLine_formatter___redArg(v_a_3703_);
return v___x_3707_;
}
}
LEAN_EXPORT void l_Lean_ppLine_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3702_ = stack[0].m_obj;
lean_object* v_a_3703_ = stack[1].m_obj;
lean_object* v_a_3704_ = stack[2].m_obj;
lean_object* v_a_3705_ = stack[3].m_obj;
lean_object* v_res_3708_;
v_res_3708_ = l_Lean_ppLine_formatter(v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
stack->m_obj
 = v_res_3708_;
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___boxed(lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_ppLine_formatter(v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
return v_res_3714_;
}
}
lean_object* l_Lean_ppRealFill_formatter(lean_object* v_p_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_PrettyPrinter_Formatter_fill(v_p_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3721_;
}
}
LEAN_EXPORT void l_Lean_ppRealFill_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3715_ = stack[0].m_obj;
lean_object* v_a_3716_ = stack[1].m_obj;
lean_object* v_a_3717_ = stack[2].m_obj;
lean_object* v_a_3718_ = stack[3].m_obj;
lean_object* v_a_3719_ = stack[4].m_obj;
lean_object* v_res_3722_;
v_res_3722_ = l_Lean_ppRealFill_formatter(v_p_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
stack->m_obj
 = v_res_3722_;
}
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter___boxed(lean_object* v_p_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_ppRealFill_formatter(v_p_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
return v_res_3729_;
}
}
lean_object* l_Lean_ppRealGroup_formatter(lean_object* v_p_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_PrettyPrinter_Formatter_group(v_p_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
return v___x_3736_;
}
}
LEAN_EXPORT void l_Lean_ppRealGroup_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3730_ = stack[0].m_obj;
lean_object* v_a_3731_ = stack[1].m_obj;
lean_object* v_a_3732_ = stack[2].m_obj;
lean_object* v_a_3733_ = stack[3].m_obj;
lean_object* v_a_3734_ = stack[4].m_obj;
lean_object* v_res_3737_;
v_res_3737_ = l_Lean_ppRealGroup_formatter(v_p_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
stack->m_obj
 = v_res_3737_;
}
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter___boxed(lean_object* v_p_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_ppRealGroup_formatter(v_p_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
return v_res_3744_;
}
}
lean_object* l_Lean_ppIndent_formatter(lean_object* v_p_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = lean_box(0);
v___x_3752_ = l_Lean_PrettyPrinter_Formatter_indent(v_p_3745_, v___x_3751_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
return v___x_3752_;
}
}
LEAN_EXPORT void l_Lean_ppIndent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3745_ = stack[0].m_obj;
lean_object* v_a_3746_ = stack[1].m_obj;
lean_object* v_a_3747_ = stack[2].m_obj;
lean_object* v_a_3748_ = stack[3].m_obj;
lean_object* v_a_3749_ = stack[4].m_obj;
lean_object* v_res_3753_;
v_res_3753_ = l_Lean_ppIndent_formatter(v_p_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
stack->m_obj
 = v_res_3753_;
}
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter___boxed(lean_object* v_p_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_ppIndent_formatter(v_p_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3760_;
}
}
static lean_object* _init_l_Lean_ppDedent_formatter___closed__0(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_nat_to_int(v___x_3761_);
return v___x_3762_;
}
}
lean_object* l_Lean_ppDedent_formatter(lean_object* v_p_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3769_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3766_);
v___x_3770_ = lean_obj_once(&l_Lean_ppDedent_formatter___closed__0, &l_Lean_ppDedent_formatter___closed__0_once, _init_l_Lean_ppDedent_formatter___closed__0);
v___x_3771_ = l_Lean_Std_Format_getIndent(v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3772_ = lean_nat_to_int(v___x_3771_);
v___x_3773_ = lean_int_sub(v___x_3770_, v___x_3772_);
lean_dec(v___x_3772_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
v___x_3775_ = l_Lean_PrettyPrinter_Formatter_indent(v_p_3763_, v___x_3774_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
return v___x_3775_;
}
}
LEAN_EXPORT void l_Lean_ppDedent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3763_ = stack[0].m_obj;
lean_object* v_a_3764_ = stack[1].m_obj;
lean_object* v_a_3765_ = stack[2].m_obj;
lean_object* v_a_3766_ = stack[3].m_obj;
lean_object* v_a_3767_ = stack[4].m_obj;
lean_object* v_res_3776_;
v_res_3776_ = l_Lean_ppDedent_formatter(v_p_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
stack->m_obj
 = v_res_3776_;
}
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter___boxed(lean_object* v_p_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_ppDedent_formatter(v_p_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
return v_res_3783_;
}
}
lean_object* l_Lean_ppAllowUngrouped_formatter___redArg(lean_object* v_a_3784_){
_start:
{
lean_object* v___x_3786_; lean_object* v_stxTrav_3787_; lean_object* v_leadWord_3788_; uint8_t v_leadWordIdent_3789_; uint8_t v_isUngrouped_3790_; lean_object* v_stack_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3802_; 
v___x_3786_ = lean_st_ref_take(v_a_3784_);
v_stxTrav_3787_ = lean_ctor_get(v___x_3786_, 0);
v_leadWord_3788_ = lean_ctor_get(v___x_3786_, 1);
v_leadWordIdent_3789_ = lean_ctor_get_uint8(v___x_3786_, sizeof(void*)*3);
v_isUngrouped_3790_ = lean_ctor_get_uint8(v___x_3786_, sizeof(void*)*3 + 1);
v_stack_3791_ = lean_ctor_get(v___x_3786_, 2);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3793_ = v___x_3786_;
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_stack_3791_);
lean_inc(v_leadWord_3788_);
lean_inc(v_stxTrav_3787_);
lean_dec(v___x_3786_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; uint8_t v___x_3796_; lean_object* v___x_3798_; 
v___x_3795_ = lean_box(0);
v___x_3796_ = 0;
if (v_isShared_3794_ == 0)
{
v___x_3798_ = v___x_3793_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_stxTrav_3787_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_leadWord_3788_);
lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_stack_3791_);
lean_ctor_set_uint8(v_reuseFailAlloc_3801_, sizeof(void*)*3, v_leadWordIdent_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3801_, sizeof(void*)*3 + 1, v_isUngrouped_3790_);
v___x_3798_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_ctor_set_uint8(v___x_3798_, sizeof(void*)*3 + 2, v___x_3796_);
v___x_3799_ = lean_st_ref_put(v_a_3784_, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3795_);
return v___x_3800_;
}
}
}
}
LEAN_EXPORT void l_Lean_ppAllowUngrouped_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3784_ = stack[0].m_obj;
lean_object* v_res_3803_;
v_res_3803_ = l_Lean_ppAllowUngrouped_formatter___redArg(v_a_3784_);
stack->m_obj
 = v_res_3803_;
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg___boxed(lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_ppAllowUngrouped_formatter___redArg(v_a_3804_);
lean_dec(v_a_3804_);
return v_res_3806_;
}
}
lean_object* l_Lean_ppAllowUngrouped_formatter(lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_ppAllowUngrouped_formatter___redArg(v_a_3808_);
return v___x_3812_;
}
}
LEAN_EXPORT void l_Lean_ppAllowUngrouped_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3807_ = stack[0].m_obj;
lean_object* v_a_3808_ = stack[1].m_obj;
lean_object* v_a_3809_ = stack[2].m_obj;
lean_object* v_a_3810_ = stack[3].m_obj;
lean_object* v_res_3813_;
v_res_3813_ = l_Lean_ppAllowUngrouped_formatter(v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
stack->m_obj
 = v_res_3813_;
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_ppAllowUngrouped_formatter(v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3819_;
}
}
lean_object* l_Lean_ppDedentIfGrouped_formatter(lean_object* v_p_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_PrettyPrinter_Formatter_concat(v_p_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3874_; 
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; 
v_unused_3875_ = lean_ctor_get(v___x_3826_, 0);
lean_dec(v_unused_3875_);
v___x_3828_ = v___x_3826_;
v_isShared_3829_ = v_isSharedCheck_3874_;
goto v_resetjp_3827_;
}
else
{
lean_dec(v___x_3826_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3874_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v_isUngrouped_3833_; 
v___x_3830_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3823_);
v___x_3831_ = l_Lean_Std_Format_getIndent(v___x_3830_);
lean_dec_ref(v___x_3830_);
v___x_3832_ = lean_st_ref_get(v_a_3822_);
v_isUngrouped_3833_ = lean_ctor_get_uint8(v___x_3832_, sizeof(void*)*3 + 1);
lean_dec(v___x_3832_);
if (v_isUngrouped_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v_fst_3836_; lean_object* v_snd_3837_; lean_object* v_stxTrav_3842_; lean_object* v_leadWord_3843_; uint8_t v_leadWordIdent_3844_; uint8_t v_isUngrouped_3845_; uint8_t v_mustBeGrouped_3846_; lean_object* v_stack_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3834_ = lean_st_ref_take(v_a_3822_);
v_stxTrav_3842_ = lean_ctor_get(v___x_3834_, 0);
v_leadWord_3843_ = lean_ctor_get(v___x_3834_, 1);
v_leadWordIdent_3844_ = lean_ctor_get_uint8(v___x_3834_, sizeof(void*)*3);
v_isUngrouped_3845_ = lean_ctor_get_uint8(v___x_3834_, sizeof(void*)*3 + 1);
v_mustBeGrouped_3846_ = lean_ctor_get_uint8(v___x_3834_, sizeof(void*)*3 + 2);
v_stack_3847_ = lean_ctor_get(v___x_3834_, 2);
v___x_3848_ = lean_box(0);
v___x_3849_ = lean_array_get_size(v_stack_3847_);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_sub(v___x_3849_, v___x_3850_);
v___x_3852_ = lean_nat_dec_lt(v___x_3851_, v___x_3849_);
if (v___x_3852_ == 0)
{
lean_dec(v___x_3851_);
lean_dec(v___x_3831_);
v_fst_3836_ = v___x_3848_;
v_snd_3837_ = v___x_3834_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3866_; 
lean_inc_ref(v_stack_3847_);
lean_inc_ref(v_leadWord_3843_);
lean_inc_ref(v_stxTrav_3842_);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; lean_object* v_unused_3868_; lean_object* v_unused_3869_; 
v_unused_3867_ = lean_ctor_get(v___x_3834_, 2);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v___x_3834_, 1);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v___x_3834_, 0);
lean_dec(v_unused_3869_);
v___x_3854_ = v___x_3834_;
v_isShared_3855_ = v_isSharedCheck_3866_;
goto v_resetjp_3853_;
}
else
{
lean_dec(v___x_3834_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3866_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v_v_3856_; lean_object* v_xs_x27_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
v_v_3856_ = lean_array_fget(v_stack_3847_, v___x_3851_);
v_xs_x27_3857_ = lean_array_fset(v_stack_3847_, v___x_3851_, v___x_3848_);
v___x_3858_ = lean_obj_once(&l_Lean_ppDedent_formatter___closed__0, &l_Lean_ppDedent_formatter___closed__0_once, _init_l_Lean_ppDedent_formatter___closed__0);
v___x_3859_ = lean_nat_to_int(v___x_3831_);
v___x_3860_ = lean_int_sub(v___x_3858_, v___x_3859_);
lean_dec(v___x_3859_);
v___x_3861_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v_v_3856_);
v___x_3862_ = lean_array_fset(v_xs_x27_3857_, v___x_3851_, v___x_3861_);
lean_dec(v___x_3851_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 2, v___x_3862_);
v___x_3864_ = v___x_3854_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_stxTrav_3842_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_leadWord_3843_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v___x_3862_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, sizeof(void*)*3, v_leadWordIdent_3844_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, sizeof(void*)*3 + 1, v_isUngrouped_3845_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, sizeof(void*)*3 + 2, v_mustBeGrouped_3846_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
v_fst_3836_ = v___x_3848_;
v_snd_3837_ = v___x_3864_;
goto v___jp_3835_;
}
}
}
v___jp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3838_ = lean_st_ref_put(v_a_3822_, v_snd_3837_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v_fst_3836_);
v___x_3840_ = v___x_3828_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_fst_3836_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_dec(v___x_3831_);
v___x_3870_ = lean_box(0);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3870_);
v___x_3872_ = v___x_3828_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
return v___x_3826_;
}
}
}
LEAN_EXPORT void l_Lean_ppDedentIfGrouped_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3820_ = stack[0].m_obj;
lean_object* v_a_3821_ = stack[1].m_obj;
lean_object* v_a_3822_ = stack[2].m_obj;
lean_object* v_a_3823_ = stack[3].m_obj;
lean_object* v_a_3824_ = stack[4].m_obj;
lean_object* v_res_3876_;
v_res_3876_ = l_Lean_ppDedentIfGrouped_formatter(v_p_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
stack->m_obj
 = v_res_3876_;
}
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter___boxed(lean_object* v_p_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_ppDedentIfGrouped_formatter(v_p_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
return v_res_3883_;
}
}
lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(lean_object* v_a_3884_){
_start:
{
lean_object* v___x_3886_; uint8_t v_isUngrouped_3887_; 
v___x_3886_ = lean_st_ref_get(v_a_3884_);
v_isUngrouped_3887_ = lean_ctor_get_uint8(v___x_3886_, sizeof(void*)*3 + 1);
lean_dec(v___x_3886_);
if (v_isUngrouped_3887_ == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_ppLine_formatter___redArg(v_a_3884_);
return v___x_3888_;
}
else
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v_a_3884_);
return v___x_3889_;
}
}
}
LEAN_EXPORT void l_Lean_ppHardLineUnlessUngrouped_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3884_ = stack[0].m_obj;
lean_object* v_res_3890_;
v_res_3890_ = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(v_a_3884_);
stack->m_obj
 = v_res_3890_;
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(v_a_3891_);
lean_dec(v_a_3891_);
return v_res_3893_;
}
}
lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter(lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(v_a_3895_);
return v___x_3899_;
}
}
LEAN_EXPORT void l_Lean_ppHardLineUnlessUngrouped_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3894_ = stack[0].m_obj;
lean_object* v_a_3895_ = stack[1].m_obj;
lean_object* v_a_3896_ = stack[2].m_obj;
lean_object* v_a_3897_ = stack[3].m_obj;
lean_object* v_res_3900_;
v_res_3900_ = l_Lean_ppHardLineUnlessUngrouped_formatter(v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
stack->m_obj
 = v_res_3900_;
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_ppHardLineUnlessUngrouped_formatter(v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
return v_res_3906_;
}
}
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg(){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_3908_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppHardSpace_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3909_;
v_res_3909_ = l_Lean_Parser_ppHardSpace_parenthesizer___redArg();
stack->m_obj
 = v_res_3909_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg___boxed(lean_object* v_a_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Parser_ppHardSpace_parenthesizer___redArg();
return v_res_3911_;
}
}
lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_3917_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppHardSpace_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3912_ = stack[0].m_obj;
lean_object* v_a_3913_ = stack[1].m_obj;
lean_object* v_a_3914_ = stack[2].m_obj;
lean_object* v_a_3915_ = stack[3].m_obj;
lean_object* v_res_3918_;
v_res_3918_ = l_Lean_Parser_ppHardSpace_parenthesizer(v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
stack->m_obj
 = v_res_3918_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_Parser_ppHardSpace_parenthesizer(v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
return v_res_3924_;
}
}
lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg(){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_3926_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppSpace_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3927_;
v_res_3927_ = l_Lean_Parser_ppSpace_parenthesizer___redArg();
stack->m_obj
 = v_res_3927_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg___boxed(lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Parser_ppSpace_parenthesizer___redArg();
return v_res_3929_;
}
}
lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_3935_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppSpace_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3930_ = stack[0].m_obj;
lean_object* v_a_3931_ = stack[1].m_obj;
lean_object* v_a_3932_ = stack[2].m_obj;
lean_object* v_a_3933_ = stack[3].m_obj;
lean_object* v_res_3936_;
v_res_3936_ = l_Lean_Parser_ppSpace_parenthesizer(v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
stack->m_obj
 = v_res_3936_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_Parser_ppSpace_parenthesizer(v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
return v_res_3942_;
}
}
lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg(){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_3944_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppLine_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3945_;
v_res_3945_ = l_Lean_Parser_ppLine_parenthesizer___redArg();
stack->m_obj
 = v_res_3945_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg___boxed(lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Parser_ppLine_parenthesizer___redArg();
return v_res_3947_;
}
}
lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_3953_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppLine_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3948_ = stack[0].m_obj;
lean_object* v_a_3949_ = stack[1].m_obj;
lean_object* v_a_3950_ = stack[2].m_obj;
lean_object* v_a_3951_ = stack[3].m_obj;
lean_object* v_res_3954_;
v_res_3954_ = l_Lean_Parser_ppLine_parenthesizer(v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
stack->m_obj
 = v_res_3954_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_Parser_ppLine_parenthesizer(v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
return v_res_3960_;
}
}
lean_object* l_Lean_Parser_ppGroup_formatter(lean_object* v_p_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_alloc_closure((void*)(l_Lean_ppIndent_formatter___boxed), 6, 1);
lean_closure_set(v___x_3967_, 0, v_p_3961_);
v___x_3968_ = l_Lean_PrettyPrinter_Formatter_fill(v___x_3967_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
return v___x_3968_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppGroup_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3961_ = stack[0].m_obj;
lean_object* v_a_3962_ = stack[1].m_obj;
lean_object* v_a_3963_ = stack[2].m_obj;
lean_object* v_a_3964_ = stack[3].m_obj;
lean_object* v_a_3965_ = stack[4].m_obj;
lean_object* v_res_3969_;
v_res_3969_ = l_Lean_Parser_ppGroup_formatter(v_p_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
stack->m_obj
 = v_res_3969_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object* v_p_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_Parser_ppGroup_formatter(v_p_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
return v_res_3976_;
}
}
lean_object* l_Lean_Parser_ppRealFill_parenthesizer(lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3983_; 
lean_inc(v_a_3981_);
lean_inc_ref(v_a_3980_);
lean_inc(v_a_3979_);
lean_inc_ref(v_a_3978_);
v___x_3983_ = lean_apply_5(v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, lean_box(0));
return v___x_3983_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppRealFill_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3977_ = stack[0].m_obj;
lean_object* v_a_3978_ = stack[1].m_obj;
lean_object* v_a_3979_ = stack[2].m_obj;
lean_object* v_a_3980_ = stack[3].m_obj;
lean_object* v_a_3981_ = stack[4].m_obj;
lean_object* v_res_3984_;
v_res_3984_ = l_Lean_Parser_ppRealFill_parenthesizer(v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
stack->m_obj
 = v_res_3984_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer___boxed(lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_Parser_ppRealFill_parenthesizer(v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
return v_res_3991_;
}
}
lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v___x_3998_; 
lean_inc(v_a_3996_);
lean_inc_ref(v_a_3995_);
lean_inc(v_a_3994_);
lean_inc_ref(v_a_3993_);
v___x_3998_ = lean_apply_5(v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, lean_box(0));
return v___x_3998_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppIndent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3992_ = stack[0].m_obj;
lean_object* v_a_3993_ = stack[1].m_obj;
lean_object* v_a_3994_ = stack[2].m_obj;
lean_object* v_a_3995_ = stack[3].m_obj;
lean_object* v_a_3996_ = stack[4].m_obj;
lean_object* v_res_3999_;
v_res_3999_ = l_Lean_Parser_ppIndent_parenthesizer(v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
stack->m_obj
 = v_res_3999_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer___boxed(lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Parser_ppIndent_parenthesizer(v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
return v_res_4006_;
}
}
lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object* v_p_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v___x_4013_; 
lean_inc(v_a_4011_);
lean_inc_ref(v_a_4010_);
lean_inc(v_a_4009_);
lean_inc_ref(v_a_4008_);
v___x_4013_ = lean_apply_5(v_p_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, lean_box(0));
return v___x_4013_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppGroup_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4007_ = stack[0].m_obj;
lean_object* v_a_4008_ = stack[1].m_obj;
lean_object* v_a_4009_ = stack[2].m_obj;
lean_object* v_a_4010_ = stack[3].m_obj;
lean_object* v_a_4011_ = stack[4].m_obj;
lean_object* v_res_4014_;
v_res_4014_ = l_Lean_Parser_ppGroup_parenthesizer(v_p_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
stack->m_obj
 = v_res_4014_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object* v_p_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Parser_ppGroup_parenthesizer(v_p_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
return v_res_4021_;
}
}
lean_object* l_Lean_Parser_ppRealGroup_parenthesizer(lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v___x_4028_; 
lean_inc(v_a_4026_);
lean_inc_ref(v_a_4025_);
lean_inc(v_a_4024_);
lean_inc_ref(v_a_4023_);
v___x_4028_ = lean_apply_5(v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, lean_box(0));
return v___x_4028_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppRealGroup_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4022_ = stack[0].m_obj;
lean_object* v_a_4023_ = stack[1].m_obj;
lean_object* v_a_4024_ = stack[2].m_obj;
lean_object* v_a_4025_ = stack[3].m_obj;
lean_object* v_a_4026_ = stack[4].m_obj;
lean_object* v_res_4029_;
v_res_4029_ = l_Lean_Parser_ppRealGroup_parenthesizer(v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_);
stack->m_obj
 = v_res_4029_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer___boxed(lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Parser_ppRealGroup_parenthesizer(v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
return v_res_4036_;
}
}
lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v___x_4043_; 
lean_inc(v_a_4041_);
lean_inc_ref(v_a_4040_);
lean_inc(v_a_4039_);
lean_inc_ref(v_a_4038_);
v___x_4043_ = lean_apply_5(v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, lean_box(0));
return v___x_4043_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppDedent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4037_ = stack[0].m_obj;
lean_object* v_a_4038_ = stack[1].m_obj;
lean_object* v_a_4039_ = stack[2].m_obj;
lean_object* v_a_4040_ = stack[3].m_obj;
lean_object* v_a_4041_ = stack[4].m_obj;
lean_object* v_res_4044_;
v_res_4044_ = l_Lean_Parser_ppDedent_parenthesizer(v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
stack->m_obj
 = v_res_4044_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Parser_ppDedent_parenthesizer(v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
return v_res_4051_;
}
}
lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg(){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_4053_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4054_;
v_res_4054_ = l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg();
stack->m_obj
 = v_res_4054_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg___boxed(lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg();
return v_res_4056_;
}
}
lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer(lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_4062_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppAllowUngrouped_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4057_ = stack[0].m_obj;
lean_object* v_a_4058_ = stack[1].m_obj;
lean_object* v_a_4059_ = stack[2].m_obj;
lean_object* v_a_4060_ = stack[3].m_obj;
lean_object* v_res_4063_;
v_res_4063_ = l_Lean_Parser_ppAllowUngrouped_parenthesizer(v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
stack->m_obj
 = v_res_4063_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_Parser_ppAllowUngrouped_parenthesizer(v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
return v_res_4069_;
}
}
lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer(lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___x_4076_; 
lean_inc(v_a_4074_);
lean_inc_ref(v_a_4073_);
lean_inc(v_a_4072_);
lean_inc_ref(v_a_4071_);
v___x_4076_ = lean_apply_5(v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, lean_box(0));
return v___x_4076_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppDedentIfGrouped_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4070_ = stack[0].m_obj;
lean_object* v_a_4071_ = stack[1].m_obj;
lean_object* v_a_4072_ = stack[2].m_obj;
lean_object* v_a_4073_ = stack[3].m_obj;
lean_object* v_a_4074_ = stack[4].m_obj;
lean_object* v_res_4077_;
v_res_4077_ = l_Lean_Parser_ppDedentIfGrouped_parenthesizer(v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
stack->m_obj
 = v_res_4077_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer___boxed(lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Parser_ppDedentIfGrouped_parenthesizer(v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
return v_res_4084_;
}
}
lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg(){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_4086_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4087_;
v_res_4087_ = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg();
stack->m_obj
 = v_res_4087_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg___boxed(lean_object* v_a_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg();
return v_res_4089_;
}
}
lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_4095_;
}
}
LEAN_EXPORT void l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4090_ = stack[0].m_obj;
lean_object* v_a_4091_ = stack[1].m_obj;
lean_object* v_a_4092_ = stack[2].m_obj;
lean_object* v_a_4093_ = stack[3].m_obj;
lean_object* v_res_4096_;
v_res_4096_ = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
stack->m_obj
 = v_res_4096_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
return v_res_4102_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1(void){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l_Array_mkArray0___redArg();
return v___x_4203_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__2));
v___x_4206_ = l_String_toRawSubstring_x27(v___x_4205_);
return v___x_4206_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__7));
v___x_4213_ = l_String_toRawSubstring_x27(v___x_4212_);
return v___x_4213_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13(void){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__12));
v___x_4220_ = l_String_toRawSubstring_x27(v___x_4219_);
return v___x_4220_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__16));
v___x_4226_ = l_String_toRawSubstring_x27(v___x_4225_);
return v___x_4226_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__33));
v___x_4267_ = l_String_toRawSubstring_x27(v___x_4266_);
return v___x_4267_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43(void){
_start:
{
uint8_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = 0;
v___x_4289_ = lean_box(0);
v___x_4290_ = l_Lean_SourceInfo_fromRef(v___x_4289_, v___x_4288_);
return v___x_4290_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49(void){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4298_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__48));
v___x_4299_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4299_);
lean_ctor_set(v___x_4300_, 1, v___x_4298_);
return v___x_4300_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__50));
v___x_4303_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
lean_ctor_set(v___x_4304_, 1, v___x_4302_);
return v___x_4304_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52(void){
_start:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4305_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51);
v___x_4306_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49);
v___x_4307_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__47));
v___x_4308_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4309_ = l_Lean_Syntax_node2(v___x_4308_, v___x_4307_, v___x_4306_, v___x_4305_);
return v___x_4309_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55(void){
_start:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4316_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1);
v___x_4317_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
v___x_4318_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v___x_4317_);
lean_ctor_set(v___x_4319_, 2, v___x_4316_);
return v___x_4319_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58(void){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4326_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55);
v___x_4327_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__57));
v___x_4328_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4329_ = l_Lean_Syntax_node1(v___x_4328_, v___x_4327_, v___x_4326_);
return v___x_4329_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4336_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55);
v___x_4337_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__60));
v___x_4338_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4339_ = l_Lean_Syntax_node1(v___x_4338_, v___x_4337_, v___x_4336_);
return v___x_4339_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62(void){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4340_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__51);
v___x_4341_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__61);
v___x_4342_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__58);
v___x_4343_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__55);
v___x_4344_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__49);
v___x_4345_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__54));
v___x_4346_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4347_ = l_Lean_Syntax_node6(v___x_4346_, v___x_4345_, v___x_4344_, v___x_4343_, v___x_4342_, v___x_4341_, v___x_4343_, v___x_4340_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__63(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4348_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__62);
v___x_4349_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__52);
v___x_4350_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__45));
v___x_4351_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__43);
v___x_4352_ = l_Lean_Syntax_node2(v___x_4351_, v___x_4350_, v___x_4349_, v___x_4348_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(lean_object* v_x_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___x_4366_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; uint8_t v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v_kind_x3f_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v___x_4366_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__0));
v___x_4639_ = ((lean_object*)(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__1));
lean_inc(v_x_4358_);
v___x_4640_ = l_Lean_Syntax_isOfKind(v_x_4358_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
lean_dec(v_x_4358_);
v___x_4641_ = lean_box(1);
v___x_4642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
lean_ctor_set(v___x_4642_, 1, v_a_4360_);
return v___x_4642_;
}
else
{
lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4643_ = lean_unsigned_to_nat(1u);
v___x_4644_ = l_Lean_Syntax_getArg(v_x_4358_, v___x_4643_);
v___x_4645_ = l_Lean_Syntax_isNone(v___x_4644_);
if (v___x_4645_ == 0)
{
uint8_t v___x_4646_; 
lean_inc(v___x_4644_);
v___x_4646_ = l_Lean_Syntax_matchesNull(v___x_4644_, v___x_4643_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
lean_dec(v___x_4644_);
lean_dec(v_x_4358_);
v___x_4647_ = lean_box(1);
v___x_4648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v_a_4360_);
return v___x_4648_;
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; uint8_t v___x_4652_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = l_Lean_Syntax_getArg(v___x_4644_, v___x_4649_);
lean_dec(v___x_4644_);
v___x_4651_ = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
lean_inc(v___x_4650_);
v___x_4652_ = l_Lean_Syntax_isOfKind(v___x_4650_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
lean_dec(v___x_4650_);
lean_dec(v_x_4358_);
v___x_4653_ = lean_box(1);
v___x_4654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
lean_ctor_set(v___x_4654_, 1, v_a_4360_);
return v___x_4654_;
}
else
{
lean_object* v___x_4655_; lean_object* v_kind_x3f_4656_; lean_object* v___x_4657_; 
v___x_4655_ = lean_unsigned_to_nat(3u);
v_kind_x3f_4656_ = l_Lean_Syntax_getArg(v___x_4650_, v___x_4655_);
lean_dec(v___x_4650_);
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v_kind_x3f_4656_);
v_kind_x3f_4620_ = v___x_4657_;
v___y_4621_ = v_a_4359_;
v___y_4622_ = v_a_4360_;
goto v___jp_4619_;
}
}
}
else
{
lean_object* v___x_4658_; 
lean_dec(v___x_4644_);
v___x_4658_ = lean_box(0);
v_kind_x3f_4620_ = v___x_4658_;
v___y_4621_ = v_a_4359_;
v___y_4622_ = v_a_4360_;
goto v___jp_4619_;
}
}
v___jp_4361_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__0));
v___x_4365_ = l_Lean_Macro_throwError___redArg(v___x_4364_, v___y_4362_, v___y_4363_);
return v___x_4365_;
}
v___jp_4367_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
lean_inc_n(v___y_4375_, 6);
lean_inc_n(v___y_4390_, 21);
v___x_4395_ = l_Lean_Syntax_node1(v___y_4390_, v___y_4375_, v___y_4394_);
lean_inc_n(v___y_4393_, 4);
v___x_4396_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4393_, v___y_4391_, v___x_4395_);
v___x_4397_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__5));
v___x_4398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___y_4390_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = l_Lean_Syntax_node5(v___y_4390_, v___y_4374_, v___y_4373_, v___y_4369_, v___y_4388_, v___x_4396_, v___x_4398_);
lean_inc(v___y_4386_);
lean_inc_n(v___y_4378_, 2);
v___x_4400_ = l_Lean_Syntax_node5(v___y_4390_, v___y_4375_, v___y_4378_, v___y_4387_, v___y_4386_, v___y_4382_, v___x_4399_);
v___x_4401_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4393_, v___y_4370_, v___x_4400_);
lean_inc_n(v___y_4376_, 3);
v___x_4402_ = l_Lean_Syntax_node1(v___y_4390_, v___y_4376_, v___x_4401_);
v___x_4403_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__1);
v___x_4404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4404_, 0, v___y_4390_);
lean_ctor_set(v___x_4404_, 1, v___y_4375_);
lean_ctor_set(v___x_4404_, 2, v___x_4403_);
lean_inc_ref_n(v___x_4404_, 2);
lean_inc_n(v___y_4377_, 3);
v___x_4405_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4377_, v___x_4402_, v___x_4404_);
v___x_4406_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__3);
v___x_4407_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__4));
v___x_4408_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__5));
lean_inc_ref_n(v___y_4371_, 4);
v___x_4409_ = l_Lean_Name_mkStr3(v___x_4407_, v___x_4408_, v___y_4371_);
lean_inc(v___y_4368_);
lean_inc(v___y_4385_);
v___x_4410_ = l_Lean_addMacroScope(v___y_4385_, v___x_4409_, v___y_4368_);
v___x_4411_ = l_Lean_Name_mkStr4(v___x_4366_, v___x_4407_, v___x_4408_, v___y_4371_);
lean_inc(v___y_4380_);
v___x_4412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v___y_4380_);
lean_inc_n(v___y_4383_, 2);
v___x_4413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v___y_4383_);
v___x_4414_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4414_, 0, v___y_4390_);
lean_ctor_set(v___x_4414_, 1, v___x_4406_);
lean_ctor_set(v___x_4414_, 2, v___x_4410_);
lean_ctor_set(v___x_4414_, 3, v___x_4413_);
v___x_4415_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__6));
lean_inc(v___y_4384_);
v___x_4416_ = l_Lean_Name_append(v___y_4384_, v___x_4415_);
v___x_4417_ = l_Lean_mkIdentFrom(v___y_4386_, v___x_4416_, v___y_4372_);
v___x_4418_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4375_, v___y_4378_, v___x_4417_);
v___x_4419_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4393_, v___x_4414_, v___x_4418_);
v___x_4420_ = l_Lean_Syntax_node1(v___y_4390_, v___y_4376_, v___x_4419_);
v___x_4421_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4377_, v___x_4420_, v___x_4404_);
v___x_4422_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__8);
v___x_4423_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__9));
v___x_4424_ = l_Lean_Name_mkStr3(v___x_4407_, v___x_4423_, v___y_4371_);
v___x_4425_ = l_Lean_addMacroScope(v___y_4385_, v___x_4424_, v___y_4368_);
v___x_4426_ = l_Lean_Name_mkStr4(v___x_4366_, v___x_4407_, v___x_4423_, v___y_4371_);
v___x_4427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
lean_ctor_set(v___x_4427_, 1, v___y_4380_);
v___x_4428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
lean_ctor_set(v___x_4428_, 1, v___y_4383_);
v___x_4429_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4429_, 0, v___y_4390_);
lean_ctor_set(v___x_4429_, 1, v___x_4422_);
lean_ctor_set(v___x_4429_, 2, v___x_4425_);
lean_ctor_set(v___x_4429_, 3, v___x_4428_);
v___x_4430_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__10));
v___x_4431_ = l_Lean_Name_append(v___y_4384_, v___x_4430_);
v___x_4432_ = l_Lean_mkIdentFrom(v___y_4386_, v___x_4431_, v___y_4372_);
lean_dec(v___y_4386_);
v___x_4433_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4375_, v___y_4378_, v___x_4432_);
v___x_4434_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4393_, v___x_4429_, v___x_4433_);
v___x_4435_ = l_Lean_Syntax_node1(v___y_4390_, v___y_4376_, v___x_4434_);
v___x_4436_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4377_, v___x_4435_, v___x_4404_);
v___x_4437_ = l_Lean_Syntax_node3(v___y_4390_, v___y_4375_, v___x_4405_, v___x_4421_, v___x_4436_);
lean_inc(v___y_4389_);
v___x_4438_ = l_Lean_Syntax_node1(v___y_4390_, v___y_4389_, v___x_4437_);
lean_inc(v___y_4392_);
v___x_4439_ = l_Lean_Syntax_node2(v___y_4390_, v___y_4392_, v___y_4379_, v___x_4438_);
v___x_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
lean_ctor_set(v___x_4440_, 1, v___y_4381_);
return v___x_4440_;
}
v___jp_4441_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4468_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__11));
lean_inc_ref(v___y_4443_);
lean_inc_ref(v___y_4460_);
v___x_4469_ = l_Lean_Name_mkStr4(v___x_4366_, v___y_4460_, v___y_4443_, v___x_4468_);
v___x_4470_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr_formatter___closed__3));
lean_inc_n(v___y_4464_, 4);
v___x_4471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___y_4464_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__13);
v___x_4473_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__14));
lean_inc_n(v___y_4442_, 2);
lean_inc_n(v___y_4459_, 2);
v___x_4474_ = l_Lean_addMacroScope(v___y_4459_, v___x_4473_, v___y_4442_);
lean_inc_n(v___y_4457_, 2);
v___x_4475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4475_, 0, v___y_4464_);
lean_ctor_set(v___x_4475_, 1, v___x_4472_);
lean_ctor_set(v___x_4475_, 2, v___x_4474_);
lean_ctor_set(v___x_4475_, 3, v___y_4457_);
v___x_4476_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__15));
v___x_4477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___y_4464_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
v___x_4478_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__17);
v___x_4479_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__18));
v___x_4480_ = l_Lean_addMacroScope(v___y_4459_, v___x_4479_, v___y_4442_);
v___x_4481_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__20));
lean_inc(v___y_4453_);
v___x_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
lean_ctor_set(v___x_4482_, 1, v___y_4453_);
v___x_4483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
lean_ctor_set(v___x_4483_, 1, v___y_4457_);
v___x_4484_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4484_, 0, v___y_4464_);
lean_ctor_set(v___x_4484_, 1, v___x_4478_);
lean_ctor_set(v___x_4484_, 2, v___x_4480_);
lean_ctor_set(v___x_4484_, 3, v___x_4483_);
if (lean_obj_tag(v___y_4455_) == 0)
{
lean_object* v___x_4485_; 
lean_inc(v___y_4454_);
lean_inc(v___y_4453_);
v___x_4485_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Lean_quoteNameMk(v___y_4454_);
v___y_4368_ = v___y_4442_;
v___y_4369_ = v___x_4475_;
v___y_4370_ = v___y_4444_;
v___y_4371_ = v___y_4447_;
v___y_4372_ = v___y_4446_;
v___y_4373_ = v___x_4471_;
v___y_4374_ = v___x_4469_;
v___y_4375_ = v___y_4449_;
v___y_4376_ = v___y_4448_;
v___y_4377_ = v___y_4450_;
v___y_4378_ = v___y_4451_;
v___y_4379_ = v___y_4452_;
v___y_4380_ = v___y_4453_;
v___y_4381_ = v___y_4456_;
v___y_4382_ = v___y_4467_;
v___y_4383_ = v___y_4457_;
v___y_4384_ = v___y_4458_;
v___y_4385_ = v___y_4459_;
v___y_4386_ = v___y_4461_;
v___y_4387_ = v___y_4462_;
v___y_4388_ = v___x_4477_;
v___y_4389_ = v___y_4463_;
v___y_4390_ = v___y_4464_;
v___y_4391_ = v___x_4484_;
v___y_4392_ = v___y_4465_;
v___y_4393_ = v___y_4466_;
v___y_4394_ = v___x_4486_;
goto v___jp_4367_;
}
else
{
lean_object* v_val_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec(v___y_4454_);
v_val_4487_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_val_4487_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4488_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__21));
lean_inc_ref(v___y_4443_);
lean_inc_ref(v___y_4460_);
v___x_4489_ = l_Lean_Name_mkStr4(v___x_4366_, v___y_4460_, v___y_4443_, v___x_4488_);
v___x_4490_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0));
v___x_4491_ = lean_string_intercalate(v___x_4490_, v_val_4487_);
lean_inc_ref(v___y_4445_);
v___x_4492_ = lean_string_append(v___y_4445_, v___x_4491_);
lean_dec_ref(v___x_4491_);
v___x_4493_ = lean_box(2);
v___x_4494_ = l_Lean_Syntax_mkNameLit(v___x_4492_, v___x_4493_);
v___x_4495_ = lean_unsigned_to_nat(1u);
v___x_4496_ = lean_mk_empty_array_with_capacity(v___x_4495_);
v___x_4497_ = lean_array_push(v___x_4496_, v___x_4494_);
v___x_4498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4493_);
lean_ctor_set(v___x_4498_, 1, v___x_4489_);
lean_ctor_set(v___x_4498_, 2, v___x_4497_);
v___y_4368_ = v___y_4442_;
v___y_4369_ = v___x_4475_;
v___y_4370_ = v___y_4444_;
v___y_4371_ = v___y_4447_;
v___y_4372_ = v___y_4446_;
v___y_4373_ = v___x_4471_;
v___y_4374_ = v___x_4469_;
v___y_4375_ = v___y_4449_;
v___y_4376_ = v___y_4448_;
v___y_4377_ = v___y_4450_;
v___y_4378_ = v___y_4451_;
v___y_4379_ = v___y_4452_;
v___y_4380_ = v___y_4453_;
v___y_4381_ = v___y_4456_;
v___y_4382_ = v___y_4467_;
v___y_4383_ = v___y_4457_;
v___y_4384_ = v___y_4458_;
v___y_4385_ = v___y_4459_;
v___y_4386_ = v___y_4461_;
v___y_4387_ = v___y_4462_;
v___y_4388_ = v___x_4477_;
v___y_4389_ = v___y_4463_;
v___y_4390_ = v___y_4464_;
v___y_4391_ = v___x_4484_;
v___y_4392_ = v___y_4465_;
v___y_4393_ = v___y_4466_;
v___y_4394_ = v___x_4498_;
goto v___jp_4367_;
}
}
else
{
lean_object* v_val_4499_; 
lean_dec(v___y_4454_);
v_val_4499_ = lean_ctor_get(v___y_4455_, 0);
lean_inc(v_val_4499_);
lean_dec_ref_known(v___y_4455_, 1);
v___y_4368_ = v___y_4442_;
v___y_4369_ = v___x_4475_;
v___y_4370_ = v___y_4444_;
v___y_4371_ = v___y_4447_;
v___y_4372_ = v___y_4446_;
v___y_4373_ = v___x_4471_;
v___y_4374_ = v___x_4469_;
v___y_4375_ = v___y_4449_;
v___y_4376_ = v___y_4448_;
v___y_4377_ = v___y_4450_;
v___y_4378_ = v___y_4451_;
v___y_4379_ = v___y_4452_;
v___y_4380_ = v___y_4453_;
v___y_4381_ = v___y_4456_;
v___y_4382_ = v___y_4467_;
v___y_4383_ = v___y_4457_;
v___y_4384_ = v___y_4458_;
v___y_4385_ = v___y_4459_;
v___y_4386_ = v___y_4461_;
v___y_4387_ = v___y_4462_;
v___y_4388_ = v___x_4477_;
v___y_4389_ = v___y_4463_;
v___y_4390_ = v___y_4464_;
v___y_4391_ = v___x_4484_;
v___y_4392_ = v___y_4465_;
v___y_4393_ = v___y_4466_;
v___y_4394_ = v_val_4499_;
goto v___jp_4367_;
}
}
v___jp_4500_:
{
lean_object* v_quotContext_4510_; lean_object* v_currMacroScope_4511_; lean_object* v_ref_4512_; uint8_t v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v_quotContext_4510_ = lean_ctor_get(v___y_4503_, 1);
v_currMacroScope_4511_ = lean_ctor_get(v___y_4503_, 2);
v_ref_4512_ = lean_ctor_get(v___y_4503_, 5);
v___x_4513_ = 0;
v___x_4514_ = l_Lean_SourceInfo_fromRef(v_ref_4512_, v___x_4513_);
v___x_4515_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15___closed__1));
v___x_4516_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__22));
v___x_4517_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__23));
v___x_4518_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__24));
lean_inc_n(v___x_4514_, 4);
v___x_4519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4514_);
lean_ctor_set(v___x_4519_, 1, v___x_4517_);
v___x_4520_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__26));
v___x_4521_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice_formatter___closed__5));
v___x_4522_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__28));
v___x_4523_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__30));
v___x_4524_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__32));
v___x_4525_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__34);
v___x_4526_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__35));
v___x_4527_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__36));
lean_inc(v_currMacroScope_4511_);
lean_inc(v_quotContext_4510_);
v___x_4528_ = l_Lean_addMacroScope(v_quotContext_4510_, v___x_4527_, v_currMacroScope_4511_);
v___x_4529_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__37));
lean_inc(v___y_4504_);
v___x_4530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
lean_ctor_set(v___x_4530_, 1, v___y_4504_);
v___x_4531_ = lean_box(0);
v___x_4532_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__39));
v___x_4533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4530_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4514_);
lean_ctor_set(v___x_4534_, 1, v___x_4525_);
lean_ctor_set(v___x_4534_, 2, v___x_4528_);
lean_ctor_set(v___x_4534_, 3, v___x_4533_);
v___x_4535_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__41));
v___x_4536_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42));
v___x_4537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4514_);
lean_ctor_set(v___x_4537_, 1, v___x_4536_);
lean_inc(v___y_4507_);
lean_inc_ref(v___x_4537_);
v___x_4538_ = l_Lean_Syntax_node3(v___x_4514_, v___x_4535_, v___x_4537_, v___x_4537_, v___y_4507_);
if (lean_obj_tag(v___y_4502_) == 0)
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_obj_once(&l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__63, &l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__63_once, _init_l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__63);
lean_inc(v_quotContext_4510_);
lean_inc(v_currMacroScope_4511_);
v___y_4442_ = v_currMacroScope_4511_;
v___y_4443_ = v___x_4516_;
v___y_4444_ = v___x_4534_;
v___y_4445_ = v___x_4536_;
v___y_4446_ = v___x_4513_;
v___y_4447_ = v___x_4526_;
v___y_4448_ = v___x_4523_;
v___y_4449_ = v___x_4521_;
v___y_4450_ = v___x_4522_;
v___y_4451_ = v___y_4509_;
v___y_4452_ = v___x_4519_;
v___y_4453_ = v___y_4504_;
v___y_4454_ = v___y_4505_;
v___y_4455_ = v___y_4506_;
v___y_4456_ = v___y_4508_;
v___y_4457_ = v___x_4531_;
v___y_4458_ = v___y_4501_;
v___y_4459_ = v_quotContext_4510_;
v___y_4460_ = v___x_4515_;
v___y_4461_ = v___y_4507_;
v___y_4462_ = v___x_4538_;
v___y_4463_ = v___x_4520_;
v___y_4464_ = v___x_4514_;
v___y_4465_ = v___x_4518_;
v___y_4466_ = v___x_4524_;
v___y_4467_ = v___x_4539_;
goto v___jp_4441_;
}
else
{
lean_object* v_val_4540_; 
v_val_4540_ = lean_ctor_get(v___y_4502_, 0);
lean_inc(v_val_4540_);
lean_dec_ref_known(v___y_4502_, 1);
lean_inc(v_quotContext_4510_);
lean_inc(v_currMacroScope_4511_);
v___y_4442_ = v_currMacroScope_4511_;
v___y_4443_ = v___x_4516_;
v___y_4444_ = v___x_4534_;
v___y_4445_ = v___x_4536_;
v___y_4446_ = v___x_4513_;
v___y_4447_ = v___x_4526_;
v___y_4448_ = v___x_4523_;
v___y_4449_ = v___x_4521_;
v___y_4450_ = v___x_4522_;
v___y_4451_ = v___y_4509_;
v___y_4452_ = v___x_4519_;
v___y_4453_ = v___y_4504_;
v___y_4454_ = v___y_4505_;
v___y_4455_ = v___y_4506_;
v___y_4456_ = v___y_4508_;
v___y_4457_ = v___x_4531_;
v___y_4458_ = v___y_4501_;
v___y_4459_ = v_quotContext_4510_;
v___y_4460_ = v___x_4515_;
v___y_4461_ = v___y_4507_;
v___y_4462_ = v___x_4538_;
v___y_4463_ = v___x_4520_;
v___y_4464_ = v___x_4514_;
v___y_4465_ = v___x_4518_;
v___y_4466_ = v___x_4524_;
v___y_4467_ = v_val_4540_;
goto v___jp_4441_;
}
}
v___jp_4541_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = l_Lean_TSyntax_getId(v___y_4546_);
lean_inc(v___x_4548_);
v___x_4549_ = l_Lean_Macro_resolveGlobalName(v___x_4548_, v___y_4543_, v___y_4545_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
if (lean_obj_tag(v_a_4550_) == 1)
{
lean_object* v_head_4551_; lean_object* v_snd_4552_; 
v_head_4551_ = lean_ctor_get(v_a_4550_, 0);
v_snd_4552_ = lean_ctor_get(v_head_4551_, 1);
if (lean_obj_tag(v_snd_4552_) == 0)
{
lean_object* v_tail_4553_; 
v_tail_4553_ = lean_ctor_get(v_a_4550_, 1);
if (lean_obj_tag(v_tail_4553_) == 0)
{
lean_inc(v_snd_4552_);
lean_inc(v_head_4551_);
if (lean_obj_tag(v___y_4547_) == 0)
{
lean_object* v_a_4554_; lean_object* v_fst_4555_; lean_object* v___x_4556_; 
v_a_4554_ = lean_ctor_get(v___x_4549_, 1);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4549_, 2);
v_fst_4555_ = lean_ctor_get(v_head_4551_, 0);
lean_inc(v_fst_4555_);
lean_dec(v_head_4551_);
lean_inc(v___x_4548_);
v___x_4556_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v_snd_4552_, v___x_4548_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v___x_4557_; 
lean_inc(v___x_4548_);
v___x_4557_ = l_Lean_quoteNameMk(v___x_4548_);
v___y_4501_ = v___x_4548_;
v___y_4502_ = v___y_4542_;
v___y_4503_ = v___y_4543_;
v___y_4504_ = v_snd_4552_;
v___y_4505_ = v_fst_4555_;
v___y_4506_ = v___y_4544_;
v___y_4507_ = v___y_4546_;
v___y_4508_ = v_a_4554_;
v___y_4509_ = v___x_4557_;
goto v___jp_4500_;
}
else
{
lean_object* v_val_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_val_4558_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_val_4558_);
lean_dec_ref_known(v___x_4556_, 1);
v___x_4559_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64));
v___x_4560_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42));
v___x_4561_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0));
v___x_4562_ = lean_string_intercalate(v___x_4561_, v_val_4558_);
v___x_4563_ = lean_string_append(v___x_4560_, v___x_4562_);
lean_dec_ref(v___x_4562_);
v___x_4564_ = lean_box(2);
v___x_4565_ = l_Lean_Syntax_mkNameLit(v___x_4563_, v___x_4564_);
v___x_4566_ = lean_unsigned_to_nat(1u);
v___x_4567_ = lean_mk_empty_array_with_capacity(v___x_4566_);
v___x_4568_ = lean_array_push(v___x_4567_, v___x_4565_);
v___x_4569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4564_);
lean_ctor_set(v___x_4569_, 1, v___x_4559_);
lean_ctor_set(v___x_4569_, 2, v___x_4568_);
v___y_4501_ = v___x_4548_;
v___y_4502_ = v___y_4542_;
v___y_4503_ = v___y_4543_;
v___y_4504_ = v_snd_4552_;
v___y_4505_ = v_fst_4555_;
v___y_4506_ = v___y_4544_;
v___y_4507_ = v___y_4546_;
v___y_4508_ = v_a_4554_;
v___y_4509_ = v___x_4569_;
goto v___jp_4500_;
}
}
else
{
lean_object* v_a_4570_; lean_object* v_fst_4571_; lean_object* v_val_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v_a_4570_ = lean_ctor_get(v___x_4549_, 1);
lean_inc(v_a_4570_);
lean_dec_ref_known(v___x_4549_, 2);
v_fst_4571_ = lean_ctor_get(v_head_4551_, 0);
lean_inc(v_fst_4571_);
lean_dec(v_head_4551_);
v_val_4572_ = lean_ctor_get(v___y_4547_, 0);
lean_inc(v_val_4572_);
lean_dec_ref_known(v___y_4547_, 1);
v___x_4573_ = l_Lean_TSyntax_getString(v_val_4572_);
lean_dec(v_val_4572_);
v___x_4574_ = lean_box(0);
v___x_4575_ = l_Lean_Name_str___override(v___x_4574_, v___x_4573_);
lean_inc(v___x_4575_);
v___x_4576_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v_snd_4552_, v___x_4575_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v___x_4577_; 
v___x_4577_ = l_Lean_quoteNameMk(v___x_4575_);
v___y_4501_ = v___x_4548_;
v___y_4502_ = v___y_4542_;
v___y_4503_ = v___y_4543_;
v___y_4504_ = v_snd_4552_;
v___y_4505_ = v_fst_4571_;
v___y_4506_ = v___y_4544_;
v___y_4507_ = v___y_4546_;
v___y_4508_ = v_a_4570_;
v___y_4509_ = v___x_4577_;
goto v___jp_4500_;
}
else
{
lean_object* v_val_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
lean_dec(v___x_4575_);
v_val_4578_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_val_4578_);
lean_dec_ref_known(v___x_4576_, 1);
v___x_4579_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__64));
v___x_4580_ = ((lean_object*)(l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___closed__42));
v___x_4581_ = ((lean_object*)(l_Lean_Parser_identWithPartialTrailingDot_formatter___closed__0));
v___x_4582_ = lean_string_intercalate(v___x_4581_, v_val_4578_);
v___x_4583_ = lean_string_append(v___x_4580_, v___x_4582_);
lean_dec_ref(v___x_4582_);
v___x_4584_ = lean_box(2);
v___x_4585_ = l_Lean_Syntax_mkNameLit(v___x_4583_, v___x_4584_);
v___x_4586_ = lean_unsigned_to_nat(1u);
v___x_4587_ = lean_mk_empty_array_with_capacity(v___x_4586_);
v___x_4588_ = lean_array_push(v___x_4587_, v___x_4585_);
v___x_4589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4584_);
lean_ctor_set(v___x_4589_, 1, v___x_4579_);
lean_ctor_set(v___x_4589_, 2, v___x_4588_);
v___y_4501_ = v___x_4548_;
v___y_4502_ = v___y_4542_;
v___y_4503_ = v___y_4543_;
v___y_4504_ = v_snd_4552_;
v___y_4505_ = v_fst_4571_;
v___y_4506_ = v___y_4544_;
v___y_4507_ = v___y_4546_;
v___y_4508_ = v_a_4570_;
v___y_4509_ = v___x_4589_;
goto v___jp_4500_;
}
}
}
else
{
lean_object* v_a_4590_; 
lean_dec(v___x_4548_);
lean_dec(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec(v___y_4544_);
lean_dec(v___y_4542_);
v_a_4590_ = lean_ctor_get(v___x_4549_, 1);
lean_inc(v_a_4590_);
lean_dec_ref_known(v___x_4549_, 2);
v___y_4362_ = v___y_4543_;
v___y_4363_ = v_a_4590_;
goto v___jp_4361_;
}
}
else
{
lean_object* v_a_4591_; 
lean_dec(v___x_4548_);
lean_dec(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec(v___y_4544_);
lean_dec(v___y_4542_);
v_a_4591_ = lean_ctor_get(v___x_4549_, 1);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4549_, 2);
v___y_4362_ = v___y_4543_;
v___y_4363_ = v_a_4591_;
goto v___jp_4361_;
}
}
else
{
lean_object* v_a_4592_; 
lean_dec(v___x_4548_);
lean_dec(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec(v___y_4544_);
lean_dec(v___y_4542_);
v_a_4592_ = lean_ctor_get(v___x_4549_, 1);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4549_, 2);
v___y_4362_ = v___y_4543_;
v___y_4363_ = v_a_4592_;
goto v___jp_4361_;
}
}
else
{
lean_object* v_a_4593_; lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_dec(v___x_4548_);
lean_dec(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec(v___y_4544_);
lean_dec(v___y_4542_);
v_a_4593_ = lean_ctor_get(v___x_4549_, 0);
v_a_4594_ = lean_ctor_get(v___x_4549_, 1);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4549_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_inc(v_a_4593_);
lean_dec(v___x_4549_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4593_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
v___jp_4602_:
{
lean_object* v___x_4609_; 
v___x_4609_ = l_Lean_Syntax_getOptional_x3f(v___y_4603_);
lean_dec(v___y_4603_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_box(0);
v___y_4542_ = v___y_4608_;
v___y_4543_ = v___y_4604_;
v___y_4544_ = v___y_4607_;
v___y_4545_ = v___y_4606_;
v___y_4546_ = v___y_4605_;
v___y_4547_ = v___x_4610_;
goto v___jp_4541_;
}
else
{
lean_object* v_val_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_val_4611_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4609_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_val_4611_);
lean_dec(v___x_4609_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_val_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
v___y_4542_ = v___y_4608_;
v___y_4543_ = v___y_4604_;
v___y_4544_ = v___y_4607_;
v___y_4545_ = v___y_4606_;
v___y_4546_ = v___y_4605_;
v___y_4547_ = v___x_4616_;
goto v___jp_4541_;
}
}
}
}
v___jp_4619_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v_declName_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4623_ = lean_unsigned_to_nat(2u);
v___x_4624_ = l_Lean_Syntax_getArg(v_x_4358_, v___x_4623_);
v___x_4625_ = lean_unsigned_to_nat(3u);
v_declName_4626_ = l_Lean_Syntax_getArg(v_x_4358_, v___x_4625_);
v___x_4627_ = lean_unsigned_to_nat(4u);
v___x_4628_ = l_Lean_Syntax_getArg(v_x_4358_, v___x_4627_);
lean_dec(v_x_4358_);
v___x_4629_ = l_Lean_Syntax_getOptional_x3f(v___x_4628_);
lean_dec(v___x_4628_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v___x_4630_; 
v___x_4630_ = lean_box(0);
v___y_4603_ = v___x_4624_;
v___y_4604_ = v___y_4621_;
v___y_4605_ = v_declName_4626_;
v___y_4606_ = v___y_4622_;
v___y_4607_ = v_kind_x3f_4620_;
v___y_4608_ = v___x_4630_;
goto v___jp_4602_;
}
else
{
lean_object* v_val_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
v_val_4631_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4629_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_val_4631_);
lean_dec(v___x_4629_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_val_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
v___y_4603_ = v___x_4624_;
v___y_4604_ = v___y_4621_;
v___y_4605_ = v_declName_4626_;
v___y_4606_ = v___y_4622_;
v___y_4607_ = v_kind_x3f_4620_;
v___y_4608_ = v___x_4636_;
goto v___jp_4602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1___boxed(lean_object* v_x_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean___aux__Lean__Parser__Extra______macroRules__Lean__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(v_x_4659_, v_a_4660_, v_a_4661_);
lean_dec_ref(v_a_4660_);
return v_res_4662_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg();
return v___x_4668_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4663_ = stack[0].m_obj;
lean_object* v___y_4664_ = stack[1].m_obj;
lean_object* v___y_4665_ = stack[2].m_obj;
lean_object* v___y_4666_ = stack[3].m_obj;
lean_object* v_res_4669_;
v_res_4669_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
stack->m_obj
 = v_res_4669_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__0_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* v___y_4676_){
_start:
{
lean_inc_ref(v___y_4676_);
return v___y_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* v___y_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__2_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4677_);
lean_dec_ref(v___y_4677_);
return v_res_4678_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = lean_apply_5(v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, lean_box(0));
return v___x_4685_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4679_ = stack[0].m_obj;
lean_object* v___y_4680_ = stack[1].m_obj;
lean_object* v___y_4681_ = stack[2].m_obj;
lean_object* v___y_4682_ = stack[3].m_obj;
lean_object* v___y_4683_ = stack[4].m_obj;
lean_object* v_res_4686_;
v_res_4686_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
stack->m_obj
 = v_res_4686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__3_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
return v_res_4693_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_4695_);
return v___x_4699_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4694_ = stack[0].m_obj;
lean_object* v___y_4695_ = stack[1].m_obj;
lean_object* v___y_4696_ = stack[2].m_obj;
lean_object* v___y_4697_ = stack[3].m_obj;
lean_object* v_res_4700_;
v_res_4700_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
stack->m_obj
 = v_res_4700_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Parser_Extra_0__Lean_initFn___lam__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn___lam__5_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(lean_object* v___x_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Lean_Parser_node(v___x_4707_, v___y_4708_);
return v___x_4709_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = lean_alloc_closure((void*)(l_Lean_ppHardLineUnlessUngrouped_formatter___boxed), 5, 0);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4722_);
return v___x_4723_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = lean_alloc_closure((void*)(l_Lean_ppAllowUngrouped_formatter___boxed), 5, 0);
v___x_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
return v___x_4731_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_4789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
return v___x_4789_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = l_Lean_Parser_skip;
v___x_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
return v___x_4797_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4806_ = lean_alloc_closure((void*)(l_Lean_ppHardSpace_formatter___boxed), 5, 0);
v___x_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4806_);
return v___x_4807_;
}
}
lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4833_; lean_object* v___y_4835_; lean_object* v___y_4836_; lean_object* v___y_4837_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v___y_4876_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4890_; lean_object* v___y_4901_; lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v___y_4960_; lean_object* v___y_4970_; lean_object* v___x_4981_; lean_object* v___y_4983_; lean_object* v___x_4993_; 
v___x_4833_ = ((lean_object*)(l_Lean_Parser_patternIgnore_formatter___closed__1));
v___x_4928_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1___closed__0));
v___x_4929_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__34_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4930_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__35_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4981_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__53_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4993_ = l_Lean_Parser_registerAlias(v___x_4833_, v___x_4928_, v___x_4929_, v___x_4930_, v___x_4981_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec_ref_known(v___x_4993_, 1);
v___x_4994_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__62_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4995_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4833_, v___x_4994_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v___x_4996_; lean_object* v___x_4997_; 
lean_dec_ref_known(v___x_4995_, 1);
v___x_4996_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__64_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4997_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4833_, v___x_4996_);
v___y_4983_ = v___x_4997_;
goto v___jp_4982_;
}
else
{
v___y_4983_ = v___x_4995_;
goto v___jp_4982_;
}
}
else
{
v___y_4983_ = v___x_4993_;
goto v___jp_4982_;
}
v___jp_4834_:
{
if (lean_obj_tag(v___y_4837_) == 0)
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
lean_dec_ref_known(v___y_4837_, 1);
v___x_4838_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__7_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4839_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1___closed__1));
v___x_4840_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__8_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4841_ = l_Lean_Parser_registerAlias(v___x_4838_, v___x_4839_, v___y_4836_, v___x_4840_, v___y_4835_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec_ref_known(v___x_4841_, 1);
v___x_4842_ = lean_obj_once(&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, &l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__9_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
v___x_4843_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4838_, v___x_4842_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
lean_dec_ref_known(v___x_4843_, 1);
v___x_4844_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4845_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4838_, v___x_4844_);
return v___x_4845_;
}
else
{
return v___x_4843_;
}
}
else
{
return v___x_4841_;
}
}
else
{
lean_dec_ref(v___y_4836_);
lean_dec_ref(v___y_4835_);
return v___y_4837_;
}
}
v___jp_4846_:
{
if (lean_obj_tag(v___y_4849_) == 0)
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
lean_dec_ref_known(v___y_4849_, 1);
v___x_4850_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__11_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4851_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1___closed__1));
v___x_4852_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__12_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4847_);
lean_inc_ref(v___y_4848_);
v___x_4853_ = l_Lean_Parser_registerAlias(v___x_4850_, v___x_4851_, v___y_4848_, v___x_4852_, v___y_4847_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
lean_dec_ref_known(v___x_4853_, 1);
v___x_4854_ = lean_obj_once(&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, &l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__13_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
v___x_4855_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4850_, v___x_4854_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
lean_dec_ref_known(v___x_4855_, 1);
v___x_4856_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4857_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4850_, v___x_4856_);
v___y_4835_ = v___y_4847_;
v___y_4836_ = v___y_4848_;
v___y_4837_ = v___x_4857_;
goto v___jp_4834_;
}
else
{
v___y_4835_ = v___y_4847_;
v___y_4836_ = v___y_4848_;
v___y_4837_ = v___x_4855_;
goto v___jp_4834_;
}
}
else
{
v___y_4835_ = v___y_4847_;
v___y_4836_ = v___y_4848_;
v___y_4837_ = v___x_4853_;
goto v___jp_4834_;
}
}
else
{
lean_dec_ref(v___y_4848_);
lean_dec_ref(v___y_4847_);
return v___y_4849_;
}
}
v___jp_4858_:
{
if (lean_obj_tag(v___y_4862_) == 0)
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
lean_dec_ref_known(v___y_4862_, 1);
v___x_4863_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__14_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4864_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1___closed__1));
v___x_4865_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4866_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__16_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4867_ = l_Lean_Parser_registerAlias(v___x_4863_, v___x_4864_, v___x_4865_, v___x_4866_, v___y_4860_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec_ref_known(v___x_4867_, 1);
v___x_4868_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__18_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4869_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4863_, v___x_4868_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec_ref_known(v___x_4869_, 1);
v___x_4870_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4871_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4863_, v___x_4870_);
v___y_4847_ = v___y_4859_;
v___y_4848_ = v___y_4861_;
v___y_4849_ = v___x_4871_;
goto v___jp_4846_;
}
else
{
v___y_4847_ = v___y_4859_;
v___y_4848_ = v___y_4861_;
v___y_4849_ = v___x_4869_;
goto v___jp_4846_;
}
}
else
{
v___y_4847_ = v___y_4859_;
v___y_4848_ = v___y_4861_;
v___y_4849_ = v___x_4867_;
goto v___jp_4846_;
}
}
else
{
lean_dec_ref(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec_ref(v___y_4859_);
return v___y_4862_;
}
}
v___jp_4872_:
{
if (lean_obj_tag(v___y_4876_) == 0)
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
lean_dec_ref_known(v___y_4876_, 1);
v___x_4877_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__20_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4878_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1___closed__1));
v___x_4879_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4880_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__21_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4874_);
v___x_4881_ = l_Lean_Parser_registerAlias(v___x_4877_, v___x_4878_, v___x_4879_, v___x_4880_, v___y_4874_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
lean_dec_ref_known(v___x_4881_, 1);
v___x_4882_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__23_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4883_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4877_, v___x_4882_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
lean_dec_ref_known(v___x_4883_, 1);
v___x_4884_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4885_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4877_, v___x_4884_);
v___y_4859_ = v___y_4873_;
v___y_4860_ = v___y_4874_;
v___y_4861_ = v___y_4875_;
v___y_4862_ = v___x_4885_;
goto v___jp_4858_;
}
else
{
v___y_4859_ = v___y_4873_;
v___y_4860_ = v___y_4874_;
v___y_4861_ = v___y_4875_;
v___y_4862_ = v___x_4883_;
goto v___jp_4858_;
}
}
else
{
v___y_4859_ = v___y_4873_;
v___y_4860_ = v___y_4874_;
v___y_4861_ = v___y_4875_;
v___y_4862_ = v___x_4881_;
goto v___jp_4858_;
}
}
else
{
lean_dec_ref(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec_ref(v___y_4873_);
return v___y_4876_;
}
}
v___jp_4886_:
{
if (lean_obj_tag(v___y_4890_) == 0)
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
lean_dec_ref_known(v___y_4890_, 1);
v___x_4891_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__24_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4892_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1___closed__1));
v___x_4893_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4894_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__25_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4888_);
v___x_4895_ = l_Lean_Parser_registerAlias(v___x_4891_, v___x_4892_, v___x_4893_, v___x_4894_, v___y_4888_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
lean_dec_ref_known(v___x_4895_, 1);
v___x_4896_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__27_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4897_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4891_, v___x_4896_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_dec_ref_known(v___x_4897_, 1);
v___x_4898_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4899_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4891_, v___x_4898_);
v___y_4873_ = v___y_4887_;
v___y_4874_ = v___y_4888_;
v___y_4875_ = v___y_4889_;
v___y_4876_ = v___x_4899_;
goto v___jp_4872_;
}
else
{
v___y_4873_ = v___y_4887_;
v___y_4874_ = v___y_4888_;
v___y_4875_ = v___y_4889_;
v___y_4876_ = v___x_4897_;
goto v___jp_4872_;
}
}
else
{
v___y_4873_ = v___y_4887_;
v___y_4874_ = v___y_4888_;
v___y_4875_ = v___y_4889_;
v___y_4876_ = v___x_4895_;
goto v___jp_4872_;
}
}
else
{
lean_dec_ref(v___y_4889_);
lean_dec_ref(v___y_4888_);
lean_dec_ref(v___y_4887_);
return v___y_4890_;
}
}
v___jp_4900_:
{
if (lean_obj_tag(v___y_4904_) == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec_ref_known(v___y_4904_, 1);
v___x_4905_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__28_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4906_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1___closed__1));
v___x_4907_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4908_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__29_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4902_);
v___x_4909_ = l_Lean_Parser_registerAlias(v___x_4905_, v___x_4906_, v___x_4907_, v___x_4908_, v___y_4902_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec_ref_known(v___x_4909_, 1);
v___x_4910_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__30_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4911_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4905_, v___x_4910_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
lean_dec_ref_known(v___x_4911_, 1);
v___x_4912_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4913_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4905_, v___x_4912_);
v___y_4887_ = v___y_4901_;
v___y_4888_ = v___y_4902_;
v___y_4889_ = v___y_4903_;
v___y_4890_ = v___x_4913_;
goto v___jp_4886_;
}
else
{
v___y_4887_ = v___y_4901_;
v___y_4888_ = v___y_4902_;
v___y_4889_ = v___y_4903_;
v___y_4890_ = v___x_4911_;
goto v___jp_4886_;
}
}
else
{
v___y_4887_ = v___y_4901_;
v___y_4888_ = v___y_4902_;
v___y_4889_ = v___y_4903_;
v___y_4890_ = v___x_4909_;
goto v___jp_4886_;
}
}
else
{
lean_dec_ref(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec_ref(v___y_4901_);
return v___y_4904_;
}
}
v___jp_4914_:
{
if (lean_obj_tag(v___y_4918_) == 0)
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
lean_dec_ref_known(v___y_4918_, 1);
v___x_4919_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__31_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4920_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1___closed__1));
v___x_4921_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4922_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__32_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4916_);
v___x_4923_ = l_Lean_Parser_registerAlias(v___x_4919_, v___x_4920_, v___x_4921_, v___x_4922_, v___y_4916_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
lean_dec_ref_known(v___x_4923_, 1);
v___x_4924_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__33_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4925_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4919_, v___x_4924_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_dec_ref_known(v___x_4925_, 1);
v___x_4926_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4927_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4919_, v___x_4926_);
v___y_4901_ = v___y_4915_;
v___y_4902_ = v___y_4916_;
v___y_4903_ = v___y_4917_;
v___y_4904_ = v___x_4927_;
goto v___jp_4900_;
}
else
{
v___y_4901_ = v___y_4915_;
v___y_4902_ = v___y_4916_;
v___y_4903_ = v___y_4917_;
v___y_4904_ = v___x_4925_;
goto v___jp_4900_;
}
}
else
{
v___y_4901_ = v___y_4915_;
v___y_4902_ = v___y_4916_;
v___y_4903_ = v___y_4917_;
v___y_4904_ = v___x_4923_;
goto v___jp_4900_;
}
}
else
{
lean_dec_ref(v___y_4917_);
lean_dec_ref(v___y_4916_);
lean_dec_ref(v___y_4915_);
return v___y_4918_;
}
}
v___jp_4931_:
{
if (lean_obj_tag(v___y_4934_) == 0)
{
lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
lean_dec_ref_known(v___y_4934_, 1);
v___x_4935_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__36_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4936_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1___closed__1));
v___x_4937_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__15_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4938_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__37_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4939_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__38_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4940_ = l_Lean_Parser_registerAlias(v___x_4935_, v___x_4936_, v___x_4937_, v___x_4938_, v___x_4939_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
lean_dec_ref_known(v___x_4940_, 1);
v___x_4941_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__40_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4942_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4935_, v___x_4941_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
lean_dec_ref_known(v___x_4942_, 1);
v___x_4943_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__19_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4944_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4935_, v___x_4943_);
v___y_4915_ = v___y_4932_;
v___y_4916_ = v___x_4939_;
v___y_4917_ = v___y_4933_;
v___y_4918_ = v___x_4944_;
goto v___jp_4914_;
}
else
{
v___y_4915_ = v___y_4932_;
v___y_4916_ = v___x_4939_;
v___y_4917_ = v___y_4933_;
v___y_4918_ = v___x_4942_;
goto v___jp_4914_;
}
}
else
{
v___y_4915_ = v___y_4932_;
v___y_4916_ = v___x_4939_;
v___y_4917_ = v___y_4933_;
v___y_4918_ = v___x_4940_;
goto v___jp_4914_;
}
}
else
{
lean_dec_ref(v___y_4933_);
lean_dec_ref(v___y_4932_);
return v___y_4934_;
}
}
v___jp_4945_:
{
if (lean_obj_tag(v___y_4948_) == 0)
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_dec_ref_known(v___y_4948_, 1);
v___x_4949_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__41_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4950_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1___closed__1));
v___x_4951_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__42_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4946_);
lean_inc_ref(v___y_4947_);
v___x_4952_ = l_Lean_Parser_registerAlias(v___x_4949_, v___x_4950_, v___y_4947_, v___x_4951_, v___y_4946_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
lean_dec_ref_known(v___x_4952_, 1);
v___x_4953_ = lean_obj_once(&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, &l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__43_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
v___x_4954_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4949_, v___x_4953_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec_ref_known(v___x_4954_, 1);
v___x_4955_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4956_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4949_, v___x_4955_);
v___y_4932_ = v___y_4946_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v___x_4956_;
goto v___jp_4931_;
}
else
{
v___y_4932_ = v___y_4946_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v___x_4954_;
goto v___jp_4931_;
}
}
else
{
v___y_4932_ = v___y_4946_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v___x_4952_;
goto v___jp_4931_;
}
}
else
{
lean_dec_ref(v___y_4947_);
lean_dec_ref(v___y_4946_);
return v___y_4948_;
}
}
v___jp_4957_:
{
if (lean_obj_tag(v___y_4960_) == 0)
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
lean_dec_ref_known(v___y_4960_, 1);
v___x_4961_ = ((lean_object*)(l_Lean_termRegister__parser__alias_x28Kind_x3a_x3d___x29_____________00__closed__22));
v___x_4962_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1___closed__1));
v___x_4963_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__44_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
lean_inc_ref(v___y_4958_);
lean_inc_ref(v___y_4959_);
v___x_4964_ = l_Lean_Parser_registerAlias(v___x_4961_, v___x_4962_, v___y_4959_, v___x_4963_, v___y_4958_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
lean_dec_ref_known(v___x_4964_, 1);
v___x_4965_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__45_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4966_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4961_, v___x_4965_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
lean_dec_ref_known(v___x_4966_, 1);
v___x_4967_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4968_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4961_, v___x_4967_);
v___y_4946_ = v___y_4958_;
v___y_4947_ = v___y_4959_;
v___y_4948_ = v___x_4968_;
goto v___jp_4945_;
}
else
{
v___y_4946_ = v___y_4958_;
v___y_4947_ = v___y_4959_;
v___y_4948_ = v___x_4966_;
goto v___jp_4945_;
}
}
else
{
v___y_4946_ = v___y_4958_;
v___y_4947_ = v___y_4959_;
v___y_4948_ = v___x_4964_;
goto v___jp_4945_;
}
}
else
{
lean_dec_ref(v___y_4959_);
lean_dec_ref(v___y_4958_);
return v___y_4960_;
}
}
v___jp_4969_:
{
if (lean_obj_tag(v___y_4970_) == 0)
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
lean_dec_ref_known(v___y_4970_, 1);
v___x_4971_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__46_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4972_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1___closed__1));
v___x_4973_ = lean_obj_once(&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, &l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__47_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
v___x_4974_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__48_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4975_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__50_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4976_ = l_Lean_Parser_registerAlias(v___x_4971_, v___x_4972_, v___x_4973_, v___x_4974_, v___x_4975_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v___x_4977_; lean_object* v___x_4978_; 
lean_dec_ref_known(v___x_4976_, 1);
v___x_4977_ = lean_obj_once(&l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_, &l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extra_0__Lean_initFn___closed__51_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_);
v___x_4978_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4971_, v___x_4977_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
lean_dec_ref_known(v___x_4978_, 1);
v___x_4979_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__10_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4980_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4971_, v___x_4979_);
v___y_4958_ = v___x_4975_;
v___y_4959_ = v___x_4973_;
v___y_4960_ = v___x_4980_;
goto v___jp_4957_;
}
else
{
v___y_4958_ = v___x_4975_;
v___y_4959_ = v___x_4973_;
v___y_4960_ = v___x_4978_;
goto v___jp_4957_;
}
}
else
{
v___y_4958_ = v___x_4975_;
v___y_4959_ = v___x_4973_;
v___y_4960_ = v___x_4976_;
goto v___jp_4957_;
}
}
else
{
return v___y_4970_;
}
}
v___jp_4982_:
{
if (lean_obj_tag(v___y_4983_) == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
lean_dec_ref_known(v___y_4983_, 1);
v___x_4984_ = ((lean_object*)(l_Lean_Parser_group_formatter___closed__1));
v___x_4985_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1___closed__0));
v___x_4986_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__55_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4987_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__56_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4988_ = l_Lean_Parser_registerAlias(v___x_4984_, v___x_4985_, v___x_4986_, v___x_4987_, v___x_4981_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
lean_dec_ref_known(v___x_4988_, 1);
v___x_4989_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__58_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4990_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_4984_, v___x_4989_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
lean_dec_ref_known(v___x_4990_, 1);
v___x_4991_ = ((lean_object*)(l___private_Lean_Parser_Extra_0__Lean_initFn___closed__60_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_));
v___x_4992_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_4984_, v___x_4991_);
v___y_4970_ = v___x_4992_;
goto v___jp_4969_;
}
else
{
v___y_4970_ = v___x_4990_;
goto v___jp_4969_;
}
}
else
{
v___y_4970_ = v___x_4988_;
goto v___jp_4969_;
}
}
else
{
return v___y_4983_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4998_;
v_res_4998_ = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4998_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2____boxed(lean_object* v_a_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
return v_res_5000_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__35();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_optional___regBuiltin_Lean_Parser_optional_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_many___regBuiltin_Lean_Parser_many_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_many1___regBuiltin_Lean_Parser_many1_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_ident = _init_l_Lean_Parser_ident();
lean_mark_persistent(l_Lean_Parser_ident);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ident___regBuiltin_Lean_Parser_ident_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_identWithPartialTrailingDot = _init_l_Lean_Parser_identWithPartialTrailingDot();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot);
l_Lean_Parser_rawIdent = _init_l_Lean_Parser_rawIdent();
lean_mark_persistent(l_Lean_Parser_rawIdent);
l_Lean_Parser_hygieneInfo = _init_l_Lean_Parser_hygieneInfo();
lean_mark_persistent(l_Lean_Parser_hygieneInfo);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_hygieneInfo___regBuiltin_Lean_Parser_hygieneInfo_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_numLit = _init_l_Lean_Parser_numLit();
lean_mark_persistent(l_Lean_Parser_numLit);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_numLit___regBuiltin_Lean_Parser_numLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_hexnum = _init_l_Lean_Parser_hexnum();
lean_mark_persistent(l_Lean_Parser_hexnum);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_hexnum___regBuiltin_Lean_Parser_hexnum_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_scientificLit = _init_l_Lean_Parser_scientificLit();
lean_mark_persistent(l_Lean_Parser_scientificLit);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_scientificLit___regBuiltin_Lean_Parser_scientificLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_strLit = _init_l_Lean_Parser_strLit();
lean_mark_persistent(l_Lean_Parser_strLit);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_strLit___regBuiltin_Lean_Parser_strLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_charLit = _init_l_Lean_Parser_charLit();
lean_mark_persistent(l_Lean_Parser_charLit);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_charLit___regBuiltin_Lean_Parser_charLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_nameLit = _init_l_Lean_Parser_nameLit();
lean_mark_persistent(l_Lean_Parser_nameLit);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_nameLit___regBuiltin_Lean_Parser_nameLit_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_group___regBuiltin_Lean_Parser_group_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_many1Indent___regBuiltin_Lean_Parser_many1Indent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_manyIndent___regBuiltin_Lean_Parser_manyIndent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_patternIgnore___regBuiltin_Lean_Parser_patternIgnore_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_ppHardSpace = _init_l_Lean_Parser_ppHardSpace();
lean_mark_persistent(l_Lean_Parser_ppHardSpace);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardSpace___regBuiltin_Lean_Parser_ppHardSpace_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_ppSpace = _init_l_Lean_Parser_ppSpace();
lean_mark_persistent(l_Lean_Parser_ppSpace);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppSpace___regBuiltin_Lean_Parser_ppSpace_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_ppLine = _init_l_Lean_Parser_ppLine();
lean_mark_persistent(l_Lean_Parser_ppLine);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppLine___regBuiltin_Lean_Parser_ppLine_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealFill___regBuiltin_Lean_Parser_ppRealFill_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppRealGroup___regBuiltin_Lean_Parser_ppRealGroup_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppIndent___regBuiltin_Lean_Parser_ppIndent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppGroup___regBuiltin_Lean_Parser_ppGroup_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedent___regBuiltin_Lean_Parser_ppDedent_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_ppAllowUngrouped = _init_l_Lean_Parser_ppAllowUngrouped();
lean_mark_persistent(l_Lean_Parser_ppAllowUngrouped);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppAllowUngrouped___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppDedentIfGrouped___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_ppHardLineUnlessUngrouped = _init_l_Lean_Parser_ppHardLineUnlessUngrouped();
lean_mark_persistent(l_Lean_Parser_ppHardLineUnlessUngrouped);
res = l___private_Lean_Parser_Extra_0__Lean_Parser_ppHardLineUnlessUngrouped___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extra_0__Lean_initFn_00___x40_Lean_Parser_Extra_2431976320____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Hygiene(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Lean_Hygiene(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
