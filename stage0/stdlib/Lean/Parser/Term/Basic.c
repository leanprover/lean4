// Lean compiler output
// Module: Lean.Parser.Term.Basic
// Imports: public import Lean.Parser.Attr public import Lean.Parser.Level public import Lean.Parser.Term.Doc meta import Lean.Parser.Basic public meta import Lean.Parser.Extra
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
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withPosition(lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
extern lean_object* l_Lean_Parser_fieldIdx;
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppDedent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "builtin_tactic_parser"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(20, 176, 46, 125, 174, 255, 81, 192)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Category"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 110, 193, 251, 60, 241, 71, 65)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 111, 227, 131, 132, 235, 83, 40)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 98, 190, 37, 195, 233, 138, 133)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(81, 243, 134, 30, 103, 185, 119, 71)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 250, 20, 100, 137, 129, 151, 213)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 87, 238, 125, 164, 191, 172, 187)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(164, 216, 62, 145, 180, 186, 75, 246)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 49, 193, 77, 38, 149, 61, 149)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 232, 237, 155, 12, 139, 172, 110)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 192, 190, 80, 95, 12, 2, 55)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 226, 76, 107, 1, 15, 101, 183)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 19, 61, 237, 245, 207, 129, 50)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1563126128) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 234, 5, 237, 68, 236, 212, 212)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 83, 218, 236, 18, 193, 210, 53)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 198, 40, 74, 198, 1, 240, 69)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(117, 95, 92, 8, 88, 47, 163, 58)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tactic_parser"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 200, 46, 177, 115, 60, 146, 227)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser(lean_object*);
static const lean_string_object l_Lean_Parser_convParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Parser_convParser___closed__0 = (const lean_object*)&l_Lean_Parser_convParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_convParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_convParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Parser_convParser___closed__1 = (const lean_object*)&l_Lean_Parser_convParser___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_convParser(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0;
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4;
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7;
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sepByIndentSemicolon"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(170, 99, 196, 249, 102, 11, 22, 231)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 349, .m_capacity = 349, .m_length = 348, .m_data = "`sepByIndentSemicolon(p)` parses a sequence of `p` optionally followed by `;`,\nsimilar to `manyIndent(p \";\"\?)`, except that if two occurrences of `p` occur on the same line,\nthe `;` is mandatory. This is used by tactic parsing, so that\n```\nexample := by\n  skip\n  skip\n```\nis legal, but `by skip skip` is not - it must be written as `by skip; skip`."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sepBy1IndentSemicolon"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 122, 81, 170, 140, 136, 141, 66)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 362, .m_capacity = 362, .m_length = 361, .m_data = "`sepBy1IndentSemicolon(p)` parses a (nonempty) sequence of `p` optionally followed by `;`,\nsimilar to `many1Indent(p \";\"\?)`, except that if two occurrences of `p` occur on the same line,\nthe `;` is mandatory. This is used by tactic parsing, so that\n```\nexample := by\n  skip\n  skip\n```\nis legal, but `by skip skip` is not - it must be written as `by skip; skip`."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 141, 160, 225, 89, 107, 71, 117)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 113, 252, 92, 83, 246, 160, 172)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented;
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2;
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5;
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 130, .m_data = "The syntax `{ tacs }` is an alternative syntax for `· tacs`.\nIt runs the tactics in sequence, and fails if the goal is not solved."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_tacticParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 28, 43, 150, 183, 142, 81, 15)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 209, 129, 56, 116, 223, 51, 73)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 70, 11, 167, 226, 145, 9, 201)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_tacticParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppLine_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppDedent_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__7_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__8_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__8_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__9_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__9_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 119, 215, 182, 191, 114, 165, 30)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 13, 185, 142, 76, 107, 137, 177)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 229, 96, 2, 142, 147, 226, 101)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq___closed__0;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = "A sequence of tactics in brackets, or a delimiter-free indented sequence of tactics.\nDelimiter-free indentation is determined by the *first* tactic of the sequence."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_node_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticSeqIndentGt"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 164, 99, 10, 143, 215, 5, 182)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 71, 140, 7, 47, 84, 129, 16)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "indented tactic sequence"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 256, .m_capacity = 256, .m_length = 255, .m_data = "Same as [`tacticSeq`] but requires delimiter-free tactic sequence to have strict indentation.\nFalls back to an empty tactic sequence when no appropriately indented content follows, producing\nan elaboration error (unsolved goals) rather than a parse error."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_seq1_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Lean_Parser_Tactic_seq1_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l_Lean_Parser_Tactic_seq1_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_seq1_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ";\n"};
static const lean_object* l_Lean_Parser_Tactic_seq1_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_seq1_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_seq1_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Tactic_seq1_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_seq1_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 140, 213, 31, 38, 205, 32, 123)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 68, 6, 57, 113, 151, 68, 138)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_seq1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_seq1___closed__0;
static lean_once_cell_t l_Lean_Parser_Tactic_seq1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_seq1___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_seq1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_seq1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1;
static const lean_string_object l_Lean_Parser_Term_hole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Parser_Term_hole___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Parser_Term_hole___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_hole___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_hole___closed__2;
static const lean_string_object l_Lean_Parser_Term_hole___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_Term_hole___closed__3 = (const lean_object*)&l_Lean_Parser_Term_hole___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_hole___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_hole___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_hole___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_hole___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_hole___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_hole___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_hole___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_hole___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 813, .m_capacity = 813, .m_length = 812, .m_data = "A *hole* (or *placeholder term*), which stands for an unknown term that is expected to be inferred based on context.\nFor example, in `@id _ Nat.zero`, the `_` must be the type of `Nat.zero`, which is `Nat`.\n\nThe way this works is that holes create fresh metavariables.\nThe elaborator is allowed to assign terms to metavariables while it is checking definitional equalities.\nThis is often known as *unification*.\n\nNormally, all holes must be solved for. However, there are a few contexts where this is not necessary:\n* In `match` patterns, holes are catch-all patterns.\n* In some tactics, such as `refine'` and `apply`, unsolved-for placeholders become new goals.\n\nRelated concept: implicit parameters are automatically filled in with holes during the elaboration process.\n\nSee also `\?m` syntax (synthetic holes)."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(144) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_hole_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_hole_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_hole_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_hole_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_hole_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_hole_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 229, 9, 16, 12, 224, 229, 201)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_hole_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_hole_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_hole_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_hole_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_hole_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_hole_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 251, 253, 165, 169, 88, 32, 49)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_syntheticHole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Parser_Term_syntheticHole___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___closed__1 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__2;
static const lean_string_object l_Lean_Parser_Term_syntheticHole___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Parser_Term_syntheticHole___closed__3 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_syntheticHole___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_syntheticHole___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3165, .m_capacity = 3165, .m_length = 3150, .m_data = "A *synthetic hole* (or *synthetic placeholder*), which stands for an unknown term that should be synthesized using tactics.\n- `\?_` creates a fresh metavariable with an auto-generated name.\n- `\?m` either refers to a pre-existing metavariable named `m` or creates a fresh metavariable with that name.\n\nIn particular, the synthetic hole syntax creates \"synthetic opaque metavariables\",\nthe same kind of metavariable used to represent goals in the tactic state.\n\nSynthetic holes are similar to holes in that `_` also creates metavariables,\nbut synthetic opaque metavariables have some different properties:\n- In tactics such as `refine`, only synthetic holes yield new goals.\n- During elaboration, unification will not solve for synthetic opaque metavariables, they are \"opaque\".\n  This is to prevent counterintuitive behavior such as disappearing goals.\n- When synthetic holes appear under binders, they capture local variables using a more complicated mechanism known as delayed assignment.\n\n## Delayed assigned metavariables\n\nThis section gives an overview of some technical details of synthetic holes, which you should feel free to skip.\nUnderstanding delayed assignments is mainly useful for those who are working on tactics and other metaprogramming.\nIt is included here until there is a suitable place for it in the reference manual.\n\nWhen a synthetic hole appears under a binding construct, such as for example `fun (x : α) (y : β) => \?s`,\nthe system creates a *delayed assignment*. This consists of\n1. A metavariable `\?m` of type `(x : α) → (y : β) → γ x y` whose local context is the local context outside the `fun`,\n  where `γ x y` is the type of `\?s`. Recall that `x` and `y` appear in the local context of `\?s`.\n2. A delayed assignment record associating `\?m` to `\?s` and the variables `#[x, y]` in the local context of `\?s`\n\nThen, this function elaborates as `fun (x : α) (y : β) => \?m x y`, where one should understand `x` and `y` here\nas being De Bruijn indexes, since Lean uses the locally nameless encoding of lambda calculus.\n\nOnce `\?s` is fully solved for, in the sense that after metavariable instantiation it is a metavariable-free term `e`,\nthen we can make the assignment `\?m := fun (x' : α) (y' : β) => e[x := x', y := y']`.\n(Implementation note: Lean only instantiates full applications `\?m x' y'` of delayed assigned metavariables, to skip forming this function.)\nThis delayed assignment mechanism is essential to the operation of basic tactics like `intro`,\nand a good mental model is that it is a way to \"apply\" the metavariable `\?s` by substituting values in for some of its local variables.\nWhile it would be easier to immediately assign `\?s := \?m x y`,\ndelayed assignment preserves `\?s` as an unsolved-for metavariable with a local context that still contains `x` and `y`,\nwhich is exactly what tactics like `intro` need.\n\nBy default, delayed assigned metavariables pretty print with what they are delayed assigned to.\nThe delayed assigned metavariables themselves can be pretty printed using `set_option pp.mvars.delayed true`.\n\nFor more information, see the \"Gruesome details\" module docstrings in `Lean.MetavarContext`."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(148) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 87, 196, 54, 9, 128, 178, 139)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 25, 118, 219, 8, 203, 22, 194)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_omission___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "omission"};
static const lean_object* l_Lean_Parser_Term_omission___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_object* l_Lean_Parser_Term_omission___closed__1 = (const lean_object*)&l_Lean_Parser_Term_omission___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_omission___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_omission___closed__2;
static const lean_string_object l_Lean_Parser_Term_omission___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⋯"};
static const lean_object* l_Lean_Parser_Term_omission___closed__3 = (const lean_object*)&l_Lean_Parser_Term_omission___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_omission___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_omission___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_omission___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_omission___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_omission___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_omission___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_omission___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_omission___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 434, .m_capacity = 434, .m_length = 427, .m_data = "The `⋯` term denotes a term that was omitted by the pretty printer.\nThe presence of `⋯` in pretty printer output is controlled by the `pp.deepTerms` and `pp.proofs` options,\nand these options can be further adjusted using `pp.deepTerms.threshold` and `pp.proofs.threshold`.\n\nIt is only meant to be used for pretty printing.\nHowever, in case it is copied and pasted from the Infoview, `⋯` logs a warning and elaborates like `_`."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(158) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_omission_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_omission_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_omission_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_omission_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_omission_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_omission_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 172, 62, 233, 244, 85, 47, 109)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_omission_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_omission_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_omission_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_omission_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_omission_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_omission_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 133, 194, 146, 208, 209, 34, 77)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_binderIdent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderIdent___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent;
static const lean_string_object l_Lean_Parser_Term_binderType_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Parser_Term_binderType_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_binderType_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_binderType_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_binderType_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_binderType_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_binderType_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_binderType_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__3_value;
static const lean_string_object l_Lean_Parser_Term_binderType_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_Term_binderType_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Term_binderType_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_Term_binderType_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_binderType_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_binderType_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_binderType_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_binderType_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_binderType_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_binderType_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_binderType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderType___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_binderType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderType___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_binderType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderType___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_binderType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderType___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_binderType___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderType___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_binderTactic_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderTactic"};
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_binderTactic_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__2_value;
static const lean_string_object l_Lean_Parser_Term_binderTactic_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__4_value;
static const lean_string_object l_Lean_Parser_Term_binderTactic_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " by "};
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__4_value),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic_formatter___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 165, 164, 143, 129, 158, 74, 4)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 3, 105, 152, 28, 10, 167, 0)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_binderTactic___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderTactic___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic;
static const lean_string_object l_Lean_Parser_Term_binderDefault___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binderDefault"};
static const lean_object* l_Lean_Parser_Term_binderDefault___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderDefault___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_binderDefault___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_binderDefault___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_binderDefault___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_binderDefault___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 119, 214, 97, 198, 223, 242, 31)}};
static const lean_object* l_Lean_Parser_Term_binderDefault___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_binderDefault___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderDefault___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_binderDefault___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderDefault___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_binderDefault___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderDefault___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_binderDefault___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderDefault___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_binderDefault___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_binderDefault___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Term_binderDefault_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_parenthesizer___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderDefault_parenthesizer___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Term_explicitBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Parser_Term_explicitBinder___closed__0 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_explicitBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_explicitBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_explicitBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_explicitBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Parser_Term_explicitBinder___closed__1 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder___closed__2;
static const lean_string_object l_Lean_Parser_Term_explicitBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Term_explicitBinder___closed__3 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder___closed__7;
static const lean_string_object l_Lean_Parser_Term_explicitBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Term_explicitBinder___closed__8 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 146, .m_capacity = 146, .m_length = 145, .m_data = "Explicit binder, like `(x y : A)` or `(x y)`.\nDefault values can be specified using `(x : A := v)` syntax, and tactics using `(x : A := by tac)`."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_implicitBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l_Lean_Parser_Term_implicitBinder___closed__0 = (const lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_implicitBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_implicitBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_implicitBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_implicitBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l_Lean_Parser_Term_implicitBinder___closed__1 = (const lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_implicitBinder___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_implicitBinder___closed__2;
static const lean_string_object l_Lean_Parser_Term_implicitBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Parser_Term_implicitBinder___closed__3 = (const lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_implicitBinder___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_implicitBinder___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 378, .m_capacity = 378, .m_length = 377, .m_data = "Implicit binder, like `{x y : A}` or `{x y}`.\nIn regular applications, whenever all parameters before it have been specified,\nthen a `_` placeholder is automatically inserted for this parameter.\nImplicit parameters should be able to be determined from the other arguments and the return type\nby unification.\n\nIn `@` explicit mode, implicit binders behave like explicit binders."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0;
static const lean_string_object l_Lean_Parser_Term_strictImplicitLeftBracket___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__1 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__1_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4;
static const lean_string_object l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket___closed__2;
static const lean_string_object l_Lean_Parser_Term_strictImplicitRightBracket___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket___closed__3 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket;
static const lean_string_object l_Lean_Parser_Term_strictImplicitBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "strictImplicitBinder"};
static const lean_object* l_Lean_Parser_Term_strictImplicitBinder___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_strictImplicitBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_strictImplicitBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_strictImplicitBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_strictImplicitBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 223, 215, 186, 222, 17, 242, 189)}};
static const lean_object* l_Lean_Parser_Term_strictImplicitBinder___closed__1 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitBinder___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitBinder___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 782, .m_capacity = 782, .m_length = 751, .m_data = "Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`.\nIn contrast to `{ ... }` implicit binders, strict-implicit binders do not automatically insert\na `_` placeholder until at least one subsequent explicit parameter is specified.\nDo *not* use strict-implicit binders unless there is a subsequent explicit parameter.\nAssuming this rule is followed, for fully applied expressions implicit and strict-implicit binders have the same behavior.\n\nExample: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`,\nthen `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter,\nand `h hs` has type `p y`.\nIn contrast, if `h' : ∀ {x : A}, x ∈ s → p x`, then `h` by itself elaborates to have type `\?m ∈ s → p \?m`\nwith `\?m` a fresh metavariable."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_optIdent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optIdent___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_optIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optIdent___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_optIdent___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optIdent___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent;
static const lean_string_object l_Lean_Parser_Term_instBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l_Lean_Parser_Term_instBinder___closed__0 = (const lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_instBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_instBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_instBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_instBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l_Lean_Parser_Term_instBinder___closed__1 = (const lean_object*)&l_Lean_Parser_Term_instBinder___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__2;
static const lean_string_object l_Lean_Parser_Term_instBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Term_instBinder___closed__3 = (const lean_object*)&l_Lean_Parser_Term_instBinder___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__6;
static const lean_string_object l_Lean_Parser_Term_instBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Term_instBinder___closed__7 = (const lean_object*)&l_Lean_Parser_Term_instBinder___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__11;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__12;
static lean_once_cell_t l_Lean_Parser_Term_instBinder___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 429, .m_capacity = 429, .m_length = 428, .m_data = "Instance-implicit binder, like `[C]` or `[inst : C]`.\nIn regular applications without `@` explicit mode, it is automatically inserted\nand solved for by typeclass inference for the specified class `C`.\nIn `@` explicit mode, if `_` is used for an instance-implicit parameter, then it is still solved for by typeclass inference;\nuse `(_)` to inhibit this and have it be solved for by unification instead, like an implicit argument."};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_binderDefault_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__0_value),((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_binderDefault_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_binderDefault_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__4_value),((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_binderDefault_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_binderDefault_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_binderDefault_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 119, 214, 97, 198, 223, 242, 31)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 200, 15, 206, 200, 98, 47, 188)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_explicitBinder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_explicitBinder_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_explicitBinder_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_explicitBinder_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder_formatter___closed__4;
static const lean_closure_object l_Lean_Parser_Term_explicitBinder_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__8_value)} };
static const lean_object* l_Lean_Parser_Term_explicitBinder_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_implicitBinder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_implicitBinder_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_implicitBinder_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_optIdent_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_optIdent_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optIdent_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_optIdent_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optIdent_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_optIdent_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_optIdent_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_instBinder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_instBinder_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_instBinder_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_instBinder_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__3;
static const lean_closure_object l_Lean_Parser_Term_instBinder_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__7_value)} };
static const lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_instBinder_formatter___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_formatter___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 181, 168, 154, 36, 105, 180, 29)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_bracketedBinder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bracketedBinder"};
static const lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 236, 200, 246, 105, 131, 38, 240)}};
static const lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_bracketedBinder_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4;
static const lean_closure_object l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_explicitBinder___closed__8_value)} };
static const lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_implicitBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_optIdent_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_optIdent_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optIdent_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_instBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_instBinder_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_instBinder_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_instBinder_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__3;
static const lean_closure_object l_Lean_Parser_Term_instBinder_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder___closed__7_value)} };
static const lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Term_instBinder_parenthesizer___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_instBinder_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 46, 136, 228, 180, 199, 157, 185)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_bracketedBinder___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_bracketedBinder___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 327, .m_capacity = 327, .m_length = 322, .m_data = "A `bracketedBinder` matches any kind of binder group that uses some kind of brackets:\n* An explicit binder like `(x y : A)`\n* An implicit binder like `{x y : A}`\n* A strict implicit binder, `⦃y z : A⦄` or its ASCII alternative `{{y z : A}}`\n* An instance binder `[A]` or `[x : A]` (multiple variables are not allowed here)"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_typeSpec_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Parser_Term_typeSpec_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_typeSpec_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Parser_Term_typeSpec_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_typeSpec_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_typeSpec_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_typeSpec_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_typeSpec_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 173, 248, 77, 70, 111, 216, 115)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 253, 28, 94, 107, 59, 142, 182)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_typeSpec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_typeSpec___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_typeSpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_typeSpec___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_typeSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_typeSpec___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_typeSpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_typeSpec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_optType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "builtin_structInstFieldDecl_parser"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 241, 24, 32, 102, 74, 183, 216)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "structInstFieldDecl"};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 206, 83, 2, 15, 157, 185, 163)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 144, 122, 62, 10, 18, 135, 243)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 127, 234, 139, 140, 202, 213, 126)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 73, 13, 203, 196, 123, 146, 136)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 111, 43, 102, 127, 243, 69, 223)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 167, 201, 73, 85, 18, 224, 250)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 238, 86, 219, 128, 113, 135, 67)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 10, 255, 122, 141, 232, 91, 10)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_structInstFieldDeclParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 155, 219, 23, 195, 76, 212, 152)}};
static const lean_object* l_Lean_Parser_Term_structInstFieldDeclParser___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldDeclParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser(lean_object*);
static const lean_string_object l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__2_value;
static const lean_string_object l_Lean_Parser_Term_optEllipsis_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " .."};
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 207, 90, 31, 52, 47, 237, 191)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 107, 208, 253, 252, 167, 109, 165)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_optEllipsis___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optEllipsis___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_optEllipsis___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optEllipsis___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_optEllipsis___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optEllipsis___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_optEllipsis___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optEllipsis___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_optEllipsis___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optEllipsis___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_optEllipsis___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optEllipsis___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis;
static const lean_string_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstArrayRef"};
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 232, 167, 67, 90, 227)}};
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__3_value),((lean_object*)&l_Lean_Parser_Term_instBinder_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 232, 167, 67, 90, 227)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 119, 180, 184, 53, 176, 23, 24)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Term_instBinder_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_instBinder_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 232, 167, 67, 90, 227)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 252, 101, 22, 5, 156, 113, 37)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_structInstArrayRef___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstArrayRef___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef;
static const lean_string_object l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__4;
static const lean_string_object l_Lean_Parser_Term_structInstLVal_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__11;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__12;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_formatter___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_formatter___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 11, 50, 166, 172, 142, 234, 224)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0_value)} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__4_value),((lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_group_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 253, 40, 249, 57, 253, 160, 66)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__11;
static lean_once_cell_t l_Lean_Parser_Term_structInstLVal___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstLVal___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal;
static const lean_string_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "structInstFieldBinder"};
static const lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 136, 45, 39, 93, 2, 154)}};
static const lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_bracketedBinder_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_structInstFieldBinder___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstFieldBinder___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_structInstFieldBinder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstFieldBinder___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_structInstFieldBinder___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstFieldBinder___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_structInstFieldBinder___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstFieldBinder___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder;
static const lean_closure_object l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_optTypeForStructInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_optTypeForStructInst___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_structInstField_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstField_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__0_value;
static const lean_string_object l_Lean_Parser_Term_structInstField_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Term_structInstField_formatter___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField_formatter___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField_formatter___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Term_structInstField_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__6;
static const lean_closure_object l_Lean_Parser_Term_structInstField_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstFieldDeclParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Term_structInstField_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ppDedent_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__11;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__12;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__13;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__14;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_formatter___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_formatter___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 71, 141, 255, 254, 105, 125, 157)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Term_structInstField_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstField_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_structInstField_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppSpace_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstField_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__4;
static const lean_closure_object l_Lean_Parser_Term_structInstField_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Term_structInstField_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Term_structInstField_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppDedent_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Term_structInstField_parenthesizer___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__11;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__12;
static lean_once_cell_t l_Lean_Parser_Term_structInstField_parenthesizer___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 10, 220, 108, 68, 147, 4, 252)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__0;
static const lean_string_object l_Lean_Parser_Term_structInstField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkColGt"};
static const lean_object* l_Lean_Parser_Term_structInstField___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstField___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__3;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__4;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__5;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__6;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__7;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__8;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__9;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__10;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__11;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__12;
static lean_once_cell_t l_Lean_Parser_Term_structInstField___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_structInstField___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField;
static const lean_string_object l_Lean_Parser_Term_structInstFields_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean_Parser_Term_structInstFields_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstFields_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_structInstFields_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstFields_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFields_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstFields_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFields_formatter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstFields_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstFields_formatter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstFields_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean_Parser_Term_structInstFields_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_structInstFields_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields(lean_object*);
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_81_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_82_ = 2;
v___x_83_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_84_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_80_, v___x_81_, v___x_82_, v___x_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec_ref_known(v___x_84_, 1);
v___x_85_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_86_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_87_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_85_, v___x_86_, v___x_83_);
return v___x_87_;
}
else
{
return v___x_84_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_88_;
v_res_88_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_();
stack->m_obj
 = v_res_88_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2____boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser(lean_object* v_rbp_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_93_ = l_Lean_Parser_categoryParser(v___x_92_, v_rbp_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_convParser(lean_object* v_rbp_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Parser_convParser___closed__1));
v___x_99_ = l_Lean_Parser_categoryParser(v___x_98_, v_rbp_97_);
return v___x_99_;
}
}
lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter(lean_object* v_p_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1));
v___x_110_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_103_, v___x_109_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_103_ = stack[0].m_obj;
lean_object* v_a_104_ = stack[1].m_obj;
lean_object* v_a_105_ = stack[2].m_obj;
lean_object* v_a_106_ = stack[3].m_obj;
lean_object* v_a_107_ = stack[4].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter(v_p_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___boxed(lean_object* v_p_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter(v_p_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
return v_res_118_;
}
}
lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer(lean_object* v_p_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; 
v___x_127_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_128_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0));
v___x_129_ = 1;
v___x_130_ = l_Lean_Parser_sepByIndent_parenthesizer(v_p_121_, v___x_127_, v___x_128_, v___x_129_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_121_ = stack[0].m_obj;
lean_object* v_a_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_a_124_ = stack[3].m_obj;
lean_object* v_a_125_ = stack[4].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer(v_p_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___boxed(lean_object* v_p_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer(v_p_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_140_ = l_Lean_Parser_symbol(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__3));
v___x_146_ = l_Lean_Parser_symbol(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5));
v___x_149_ = l_Lean_Parser_checkColGe(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5));
v___x_151_ = l_Lean_Parser_checkColEq(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__8));
v___x_154_ = l_Lean_Parser_checkLinebreakBefore(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = l_Lean_Parser_pushNone;
v___x_156_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9);
v___x_157_ = l_Lean_Parser_andthen(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10);
v___x_159_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7);
v___x_160_ = l_Lean_Parser_andthen(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11);
v___x_162_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0);
v___x_163_ = l_Lean_Parser_orelse(v___x_162_, v___x_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon(lean_object* v_p_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_p_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_165_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_166_ = 1;
v___x_167_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2));
v___x_168_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4);
v_p_169_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_167_, v_p_164_, v___x_168_);
v___x_170_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6);
v___x_171_ = l_Lean_Parser_andthen(v___x_170_, v_p_169_);
v___x_172_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12);
v___x_173_ = l_Lean_Parser_sepBy(v___x_171_, v___x_165_, v___x_172_, v___x_166_);
v___x_174_ = l_Lean_Parser_withPosition(v___x_173_);
return v___x_174_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1(){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
v___x_185_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3));
v___x_186_ = l_Lean_addBuiltinDocString(v___x_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_187_;
v_res_187_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___boxed(lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
return v_res_189_;
}
}
lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(lean_object* v_p_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1));
v___x_197_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_190_, v___x_196_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_190_ = stack[0].m_obj;
lean_object* v_a_191_ = stack[1].m_obj;
lean_object* v_a_192_ = stack[2].m_obj;
lean_object* v_a_193_ = stack[3].m_obj;
lean_object* v_a_194_ = stack[4].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(v_p_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed(lean_object* v_p_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(v_p_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_205_;
}
}
lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(lean_object* v_p_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v___x_212_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_213_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0));
v___x_214_ = 1;
v___x_215_ = l_Lean_Parser_sepBy1Indent_parenthesizer(v_p_206_, v___x_212_, v___x_213_, v___x_214_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_215_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_206_ = stack[0].m_obj;
lean_object* v_a_207_ = stack[1].m_obj;
lean_object* v_a_208_ = stack[2].m_obj;
lean_object* v_a_209_ = stack[3].m_obj;
lean_object* v_a_210_ = stack[4].m_obj;
lean_object* v_res_216_;
v_res_216_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(v_p_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed(lean_object* v_p_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(v_p_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon(lean_object* v_p_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_p_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_225_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_226_ = 1;
v___x_227_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2));
v___x_228_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4);
v_p_229_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_227_, v_p_224_, v___x_228_);
v___x_230_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6);
v___x_231_ = l_Lean_Parser_andthen(v___x_230_, v_p_229_);
v___x_232_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12);
v___x_233_ = l_Lean_Parser_sepBy1(v___x_231_, v___x_225_, v___x_232_, v___x_226_);
v___x_234_ = l_Lean_Parser_withPosition(v___x_233_);
return v___x_234_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1(){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
v___x_244_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2));
v___x_245_ = l_Lean_addBuiltinDocString(v___x_243_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_246_;
v_res_246_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___boxed(lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
return v_res_248_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___y_288_; lean_object* v___x_298_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_283_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
v___x_284_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_285_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_286_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_298_ = l_Lean_Parser_registerAlias(v___x_282_, v___x_283_, v___x_284_, v___x_285_, v___x_286_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref_known(v___x_298_, 1);
v___x_299_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_300_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_282_, v___x_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref_known(v___x_300_, 1);
v___x_301_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_302_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_282_, v___x_301_);
v___y_288_ = v___x_302_;
goto v___jp_287_;
}
else
{
v___y_288_ = v___x_300_;
goto v___jp_287_;
}
}
else
{
v___y_288_ = v___x_298_;
goto v___jp_287_;
}
v___jp_287_:
{
if (lean_obj_tag(v___y_288_) == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref_known(v___y_288_, 1);
v___x_289_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_290_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
v___x_291_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_292_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_293_ = l_Lean_Parser_registerAlias(v___x_289_, v___x_290_, v___x_291_, v___x_292_, v___x_286_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref_known(v___x_293_, 1);
v___x_294_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_295_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_289_, v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref_known(v___x_295_, 1);
v___x_296_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_297_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_289_, v___x_296_);
return v___x_297_;
}
else
{
return v___x_295_;
}
}
else
{
return v___x_293_;
}
}
else
{
return v___y_288_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_303_;
v_res_303_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2____boxed(lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
return v_res_305_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2(void){
_start:
{
uint8_t v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_312_ = 0;
v___x_313_ = 1;
v___x_314_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_315_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0));
v___x_316_ = l_Lean_Parser_mkAntiquot(v___x_315_, v___x_314_, v___x_313_, v___x_312_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_319_ = l_Lean_Parser_categoryParser(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_321_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_322_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4);
v___x_323_ = lean_unsigned_to_nat(1024u);
v___x_324_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_325_ = l_Lean_Parser_leadingNode(v___x_324_, v___x_323_, v___x_322_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5);
v___x_327_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2);
v___x_328_ = l_Lean_Parser_withAntiquot(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6);
v___x_330_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_331_ = l_Lean_Parser_withCache(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2(void){
_start:
{
uint8_t v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_339_ = 0;
v___x_340_ = 1;
v___x_341_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_342_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0));
v___x_343_ = l_Lean_Parser_mkAntiquot(v___x_342_, v___x_341_, v___x_340_, v___x_339_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3));
v___x_346_ = l_Lean_Parser_symbol(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_348_ = l_Lean_Parser_Tactic_sepByIndentSemicolon(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_351_ = l_Lean_Parser_symbol(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_353_ = l_Lean_Parser_skip;
v___x_354_ = l_Lean_Parser_andthen(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8);
v___x_356_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5);
v___x_357_ = l_Lean_Parser_andthen(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9);
v___x_359_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4);
v___x_360_ = l_Lean_Parser_andthen(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10);
v___x_362_ = lean_unsigned_to_nat(1024u);
v___x_363_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_364_ = l_Lean_Parser_leadingNode(v___x_363_, v___x_362_, v___x_361_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11);
v___x_366_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2);
v___x_367_ = l_Lean_Parser_withAntiquot(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12);
v___x_369_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_370_ = l_Lean_Parser_withCache(v___x_369_, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13);
return v___x_371_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1(){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_375_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0));
v___x_376_ = l_Lean_addBuiltinDocString(v___x_374_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_377_;
v_res_377_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___boxed(lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
return v_res_379_;
}
}
lean_object* l_Lean_Parser_tacticParser_formatter___redArg(lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_386_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_385_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_Parser_tacticParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_380_ = stack[0].m_obj;
lean_object* v_a_381_ = stack[1].m_obj;
lean_object* v_a_382_ = stack[2].m_obj;
lean_object* v_a_383_ = stack[3].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_380_, v_a_381_, v_a_382_, v_a_383_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg___boxed(lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_393_;
}
}
lean_object* l_Lean_Parser_tacticParser_formatter(lean_object* v_rbp_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_395_, v_a_396_, v_a_397_, v_a_398_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Lean_Parser_tacticParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_394_ = stack[0].m_obj;
lean_object* v_a_395_ = stack[1].m_obj;
lean_object* v_a_396_ = stack[2].m_obj;
lean_object* v_a_397_ = stack[3].m_obj;
lean_object* v_a_398_ = stack[4].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_Parser_tacticParser_formatter(v_rbp_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___boxed(lean_object* v_rbp_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Parser_tacticParser_formatter(v_rbp_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_rbp_402_);
return v_res_408_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_423_ = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter___boxed), 6, 1);
lean_closure_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_427_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4);
v___x_428_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_428_, 0, v___x_427_);
lean_closure_set(v___x_428_, 1, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6);
v___x_430_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__3));
v___x_431_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_431_, 0, v___x_430_);
lean_closure_set(v___x_431_, 1, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7);
v___x_433_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__1));
v___x_434_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_434_, 0, v___x_433_);
lean_closure_set(v___x_434_, 1, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_435_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8);
v___x_436_ = lean_unsigned_to_nat(1024u);
v___x_437_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_438_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_438_, 0, v___x_437_);
lean_closure_set(v___x_438_, 1, v___x_436_);
lean_closure_set(v___x_438_, 2, v___x_435_);
return v___x_438_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__0));
v___x_445_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9);
v___x_446_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_444_, v___x_445_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
return v___x_446_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeqBracketed_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_439_ = stack[0].m_obj;
lean_object* v_a_440_ = stack[1].m_obj;
lean_object* v_a_441_ = stack[2].m_obj;
lean_object* v_a_442_ = stack[3].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(v_a_439_, v_a_440_, v_a_441_, v_a_442_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed(lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_453_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_463_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_464_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1));
v___x_465_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_466_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_462_, v___x_463_, v___x_464_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_467_;
v_res_467_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___boxed(lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
return v_res_469_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0));
v___x_489_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2));
v___x_490_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_488_, v___x_489_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_490_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeq1Indented_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_483_ = stack[0].m_obj;
lean_object* v_a_484_ = stack[1].m_obj;
lean_object* v_a_485_ = stack[2].m_obj;
lean_object* v_a_486_ = stack[3].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(v_a_483_, v_a_484_, v_a_485_, v_a_486_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed(lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_497_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9(){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_506_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_507_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0));
v___x_508_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_509_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_505_, v___x_506_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_510_;
v_res_510_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___boxed(lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_527_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_528_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_528_, 0, v___x_527_);
lean_closure_set(v___x_528_, 1, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_529_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3, &l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3);
v___x_530_ = lean_unsigned_to_nat(1024u);
v___x_531_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_532_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_532_, 0, v___x_531_);
lean_closure_set(v___x_532_, 1, v___x_530_);
lean_closure_set(v___x_532_, 2, v___x_529_);
return v___x_532_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter(lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_539_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4);
v___x_540_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_538_, v___x_539_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_540_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeq_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_533_ = stack[0].m_obj;
lean_object* v_a_534_ = stack[1].m_obj;
lean_object* v_a_535_ = stack[2].m_obj;
lean_object* v_a_536_ = stack[3].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lean_Parser_Tactic_tacticSeq_formatter(v_a_533_, v_a_534_, v_a_535_, v_a_536_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___boxed(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Parser_Tactic_tacticSeq_formatter(v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_547_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13(){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_556_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_557_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0));
v___x_558_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_559_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_555_, v___x_556_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_560_;
v_res_560_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___boxed(lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
return v_res_562_;
}
}
lean_object* l_Lean_Parser_tacticParser_parenthesizer(lean_object* v_rbp_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_570_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_569_, v_rbp_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v___x_570_;
}
}
LEAN_EXPORT void l_Lean_Parser_tacticParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_563_ = stack[0].m_obj;
lean_object* v_a_564_ = stack[1].m_obj;
lean_object* v_a_565_ = stack[2].m_obj;
lean_object* v_a_566_ = stack[3].m_obj;
lean_object* v_a_567_ = stack[4].m_obj;
lean_object* v_res_571_;
v_res_571_ = l_Lean_Parser_tacticParser_parenthesizer(v_rbp_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer___boxed(lean_object* v_rbp_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Parser_tacticParser_parenthesizer(v_rbp_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_578_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__0));
v___x_616_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__10));
v___x_617_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_615_, v___x_616_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_610_ = stack[0].m_obj;
lean_object* v_a_611_ = stack[1].m_obj;
lean_object* v_a_612_ = stack[2].m_obj;
lean_object* v_a_613_ = stack[3].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(v_a_610_, v_a_611_, v_a_612_, v_a_613_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed(lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_624_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19(){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_633_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_634_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_635_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1));
v___x_636_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_637_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_633_, v___x_634_, v___x_635_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_638_;
v_res_638_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___boxed(lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
return v_res_640_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0));
v___x_660_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2));
v___x_661_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_659_, v___x_660_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_661_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_654_ = stack[0].m_obj;
lean_object* v_a_655_ = stack[1].m_obj;
lean_object* v_a_656_ = stack[2].m_obj;
lean_object* v_a_657_ = stack[3].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(v_a_654_, v_a_655_, v_a_656_, v_a_657_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed(lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_668_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23(){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_677_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_678_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0));
v___x_679_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_676_, v___x_677_, v___x_678_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_681_;
v_res_681_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___boxed(lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
return v_res_683_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_692_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_693_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_693_, 0, v___x_692_);
lean_closure_set(v___x_693_, 1, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1);
v___x_695_ = lean_unsigned_to_nat(1024u);
v___x_696_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_697_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_697_, 0, v___x_696_);
lean_closure_set(v___x_697_, 1, v___x_695_);
lean_closure_set(v___x_697_, 2, v___x_694_);
return v___x_697_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer(lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_704_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2, &l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2);
v___x_705_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_703_, v___x_704_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
return v___x_705_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeq_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_698_ = stack[0].m_obj;
lean_object* v_a_699_ = stack[1].m_obj;
lean_object* v_a_700_ = stack[2].m_obj;
lean_object* v_a_701_ = stack[3].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Parser_Tactic_tacticSeq_parenthesizer(v_a_698_, v_a_699_, v_a_700_, v_a_701_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed(lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Parser_Tactic_tacticSeq_parenthesizer(v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_712_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27(){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_720_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_721_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_722_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0));
v___x_723_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___x_724_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_720_, v___x_721_, v___x_722_, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_725_;
v_res_725_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___boxed(lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
return v_res_727_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__0(void){
_start:
{
uint8_t v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_728_ = 0;
v___x_729_ = 1;
v___x_730_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_731_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0));
v___x_732_ = l_Lean_Parser_mkAntiquot(v___x_731_, v___x_730_, v___x_729_, v___x_728_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_734_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_735_ = l_Lean_Parser_orelse(v___x_734_, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__2(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__1, &l_Lean_Parser_Tactic_tacticSeq___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__1);
v___x_737_ = lean_unsigned_to_nat(1024u);
v___x_738_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_739_ = l_Lean_Parser_leadingNode(v___x_738_, v___x_737_, v___x_736_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__3(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__2, &l_Lean_Parser_Tactic_tacticSeq___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__2);
v___x_741_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_742_ = l_Lean_Parser_withAntiquot(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__4(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__3, &l_Lean_Parser_Tactic_tacticSeq___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__3);
v___x_744_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_745_ = l_Lean_Parser_withCache(v___x_744_, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq(void){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__4, &l_Lean_Parser_Tactic_tacticSeq___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__4);
return v___x_746_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1(){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_750_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0));
v___x_751_ = l_Lean_addBuiltinDocString(v___x_749_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_752_;
v_res_752_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___boxed(lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
return v_res_754_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_757_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_758_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_758_, 0, v___x_757_);
lean_closure_set(v___x_758_, 1, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2));
v___x_763_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1);
v___x_764_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_764_, 0, v___x_763_);
lean_closure_set(v___x_764_, 1, v___x_762_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3);
v___x_766_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_767_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_767_, 0, v___x_766_);
lean_closure_set(v___x_767_, 1, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4);
v___x_769_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_770_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_770_, 0, v___x_769_);
lean_closure_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_777_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5);
v___x_778_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_776_, v___x_777_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
return v___x_778_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_771_ = stack[0].m_obj;
lean_object* v_a_772_ = stack[1].m_obj;
lean_object* v_a_773_ = stack[2].m_obj;
lean_object* v_a_774_ = stack[3].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(v_a_771_, v_a_772_, v_a_773_, v_a_774_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_785_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3(){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_794_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_795_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_796_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1));
v___x_797_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed), 5, 0);
v___x_798_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_794_, v___x_795_, v___x_796_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_799_;
v_res_799_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___boxed(lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
return v_res_801_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_804_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_805_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_805_, 0, v___x_804_);
lean_closure_set(v___x_805_, 1, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2));
v___x_810_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1);
v___x_811_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_811_, 0, v___x_810_);
lean_closure_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3);
v___x_813_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_814_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_814_, 0, v___x_813_);
lean_closure_set(v___x_814_, 1, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4);
v___x_816_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_817_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_817_, 0, v___x_816_);
lean_closure_set(v___x_817_, 1, v___x_815_);
return v___x_817_;
}
}
lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_824_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5);
v___x_825_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_823_, v___x_824_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
return v___x_825_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_818_ = stack[0].m_obj;
lean_object* v_a_819_ = stack[1].m_obj;
lean_object* v_a_820_ = stack[2].m_obj;
lean_object* v_a_821_ = stack[3].m_obj;
lean_object* v_res_826_;
v_res_826_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(v_a_818_, v_a_819_, v_a_820_, v_a_821_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_832_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7(){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_841_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_842_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0));
v___x_843_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed), 5, 0);
v___x_844_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_840_, v___x_841_, v___x_842_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_845_;
v_res_845_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___boxed(lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
return v_res_847_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0));
v___x_850_ = l_Lean_Parser_checkColGt(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_852_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1);
v___x_853_ = l_Lean_Parser_andthen(v___x_852_, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = l_Lean_Parser_pushNone;
v___x_855_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_856_ = l_Lean_Parser_node(v___x_855_, v___x_854_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3);
v___x_858_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2);
v___x_859_ = l_Lean_Parser_orelse(v___x_858_, v___x_857_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4);
v___x_861_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_862_ = l_Lean_Parser_orelse(v___x_861_, v___x_860_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5);
v___x_864_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_865_ = l_Lean_Parser_node(v___x_864_, v___x_863_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6);
v___x_867_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_868_ = l_Lean_Parser_withAntiquot(v___x_867_, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt(void){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7);
return v___x_869_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1(){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0));
v___x_878_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1));
v___x_879_ = l_Lean_addBuiltinDocString(v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_880_;
v_res_880_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___boxed(lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
return v_res_882_;
}
}
lean_object* l_Lean_Parser_Tactic_seq1_formatter(lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_904_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__4));
v___x_905_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_903_, v___x_904_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_905_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_seq1_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_898_ = stack[0].m_obj;
lean_object* v_a_899_ = stack[1].m_obj;
lean_object* v_a_900_ = stack[2].m_obj;
lean_object* v_a_901_ = stack[3].m_obj;
lean_object* v_res_906_;
v_res_906_ = l_Lean_Parser_Tactic_seq1_formatter(v_a_898_, v_a_899_, v_a_900_, v_a_901_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter___boxed(lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Parser_Tactic_seq1_formatter(v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_912_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3(){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_920_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_921_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_922_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0));
v___x_923_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_formatter___boxed), 5, 0);
v___x_924_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_920_, v___x_921_, v___x_922_, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_925_;
v_res_925_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___boxed(lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
return v_res_927_;
}
}
lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer(lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_942_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1));
v___x_943_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_941_, v___x_942_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
return v___x_943_;
}
}
LEAN_EXPORT void l_Lean_Parser_Tactic_seq1_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_936_ = stack[0].m_obj;
lean_object* v_a_937_ = stack[1].m_obj;
lean_object* v_a_938_ = stack[2].m_obj;
lean_object* v_a_939_ = stack[3].m_obj;
lean_object* v_res_944_;
v_res_944_ = l_Lean_Parser_Tactic_seq1_parenthesizer(v_a_936_, v_a_937_, v_a_938_, v_a_939_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___boxed(lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Parser_Tactic_seq1_parenthesizer(v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_950_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7(){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_958_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_959_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_960_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0));
v___x_961_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_parenthesizer___boxed), 5, 0);
v___x_962_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_958_, v___x_959_, v___x_960_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_963_;
v_res_963_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___boxed(lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__0(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_967_ = l_Lean_Parser_symbol(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__1(void){
_start:
{
uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_968_ = 1;
v___x_969_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__0, &l_Lean_Parser_Tactic_seq1___closed__0_once, _init_l_Lean_Parser_Tactic_seq1___closed__0);
v___x_970_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_971_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_972_ = l_Lean_Parser_sepBy1(v___x_971_, v___x_970_, v___x_969_, v___x_968_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__2(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__1, &l_Lean_Parser_Tactic_seq1___closed__1_once, _init_l_Lean_Parser_Tactic_seq1___closed__1);
v___x_974_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_975_ = l_Lean_Parser_node(v___x_974_, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1(void){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__2, &l_Lean_Parser_Tactic_seq1___closed__2_once, _init_l_Lean_Parser_Tactic_seq1___closed__2);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__2(void){
_start:
{
uint8_t v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_983_ = 0;
v___x_984_ = 1;
v___x_985_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_986_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__0));
v___x_987_ = l_Lean_Parser_mkAntiquot(v___x_986_, v___x_985_, v___x_984_, v___x_983_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__4(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__3));
v___x_990_ = l_Lean_Parser_symbol(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__5(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_992_ = lean_unsigned_to_nat(1024u);
v___x_993_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_994_ = l_Lean_Parser_leadingNode(v___x_993_, v___x_992_, v___x_991_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__6(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__5, &l_Lean_Parser_Term_hole___closed__5_once, _init_l_Lean_Parser_Term_hole___closed__5);
v___x_996_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__2, &l_Lean_Parser_Term_hole___closed__2_once, _init_l_Lean_Parser_Term_hole___closed__2);
v___x_997_ = l_Lean_Parser_withAntiquot(v___x_996_, v___x_995_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__7(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__6, &l_Lean_Parser_Term_hole___closed__6_once, _init_l_Lean_Parser_Term_hole___closed__6);
v___x_999_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1000_ = l_Lean_Parser_withCache(v___x_999_, v___x_998_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__7, &l_Lean_Parser_Term_hole___closed__7_once, _init_l_Lean_Parser_Term_hole___closed__7);
return v___x_1001_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1(){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1007_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1008_ = l_Lean_Parser_Term_hole;
v___x_1009_ = lean_unsigned_to_nat(1000u);
v___x_1010_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1006_, v___x_1007_, v___x_1008_, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1011_;
v_res_1011_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___boxed(lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
return v_res_1013_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3(){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1017_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0));
v___x_1018_ = l_Lean_addBuiltinDocString(v___x_1016_, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1019_;
v_res_1019_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
stack->m_obj
 = v_res_1019_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___boxed(lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
return v_res_1021_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5(){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1049_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6));
v___x_1050_ = l_Lean_addBuiltinDeclarationRanges(v___x_1048_, v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1051_;
v_res_1051_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___boxed(lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
return v_res_1053_;
}
}
lean_object* l_Lean_Parser_Term_hole_formatter(lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__0));
v___x_1073_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__2));
v___x_1074_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1072_, v___x_1073_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
return v___x_1074_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_hole_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1067_ = stack[0].m_obj;
lean_object* v_a_1068_ = stack[1].m_obj;
lean_object* v_a_1069_ = stack[2].m_obj;
lean_object* v_a_1070_ = stack[3].m_obj;
lean_object* v_res_1075_;
v_res_1075_ = l_Lean_Parser_Term_hole_formatter(v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Parser_Term_hole_formatter(v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1081_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9(){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1089_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1090_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1091_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0));
v___x_1092_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1093_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1089_, v___x_1090_, v___x_1091_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1094_;
v_res_1094_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
stack->m_obj
 = v_res_1094_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___boxed(lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
return v_res_1096_;
}
}
lean_object* l_Lean_Parser_Term_hole_parenthesizer(lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__0));
v___x_1116_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__2));
v___x_1117_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1115_, v___x_1116_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1117_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_hole_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1110_ = stack[0].m_obj;
lean_object* v_a_1111_ = stack[1].m_obj;
lean_object* v_a_1112_ = stack[2].m_obj;
lean_object* v_a_1113_ = stack[3].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l_Lean_Parser_Term_hole_parenthesizer(v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Parser_Term_hole_parenthesizer(v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1124_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13(){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1132_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1133_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1134_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0));
v___x_1135_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1136_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1132_, v___x_1133_, v___x_1134_, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1137_;
v_res_1137_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
stack->m_obj
 = v_res_1137_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___boxed(lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
return v_res_1139_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__2(void){
_start:
{
uint8_t v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1146_ = 0;
v___x_1147_ = 1;
v___x_1148_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1149_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__0));
v___x_1150_ = l_Lean_Parser_mkAntiquot(v___x_1149_, v___x_1148_, v___x_1147_, v___x_1146_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__4(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__3));
v___x_1153_ = l_Lean_Parser_symbol(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__5(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_1155_ = l_Lean_Parser_ident;
v___x_1156_ = l_Lean_Parser_orelse(v___x_1155_, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__6(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__5, &l_Lean_Parser_Term_syntheticHole___closed__5_once, _init_l_Lean_Parser_Term_syntheticHole___closed__5);
v___x_1158_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__4, &l_Lean_Parser_Term_syntheticHole___closed__4_once, _init_l_Lean_Parser_Term_syntheticHole___closed__4);
v___x_1159_ = l_Lean_Parser_andthen(v___x_1158_, v___x_1157_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__7(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__6, &l_Lean_Parser_Term_syntheticHole___closed__6_once, _init_l_Lean_Parser_Term_syntheticHole___closed__6);
v___x_1161_ = lean_unsigned_to_nat(1024u);
v___x_1162_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1163_ = l_Lean_Parser_leadingNode(v___x_1162_, v___x_1161_, v___x_1160_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__8(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__7, &l_Lean_Parser_Term_syntheticHole___closed__7_once, _init_l_Lean_Parser_Term_syntheticHole___closed__7);
v___x_1165_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__2, &l_Lean_Parser_Term_syntheticHole___closed__2_once, _init_l_Lean_Parser_Term_syntheticHole___closed__2);
v___x_1166_ = l_Lean_Parser_withAntiquot(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__9(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__8, &l_Lean_Parser_Term_syntheticHole___closed__8_once, _init_l_Lean_Parser_Term_syntheticHole___closed__8);
v___x_1168_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1169_ = l_Lean_Parser_withCache(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__9, &l_Lean_Parser_Term_syntheticHole___closed__9_once, _init_l_Lean_Parser_Term_syntheticHole___closed__9);
return v___x_1170_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1(){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1173_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1174_ = l_Lean_Parser_Term_syntheticHole;
v___x_1175_ = lean_unsigned_to_nat(1000u);
v___x_1176_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1172_, v___x_1173_, v___x_1174_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1177_;
v_res_1177_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
stack->m_obj
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1___boxed(lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
return v_res_1179_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3(){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1183_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0));
v___x_1184_ = l_Lean_addBuiltinDocString(v___x_1182_, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1185_;
v_res_1185_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
stack->m_obj
 = v_res_1185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___boxed(lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
return v_res_1187_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5(){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1215_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6));
v___x_1216_ = l_Lean_addBuiltinDeclarationRanges(v___x_1214_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1217_;
v_res_1217_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___boxed(lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
return v_res_1219_;
}
}
lean_object* l_Lean_Parser_Term_syntheticHole_formatter(lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__0));
v___x_1246_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__5));
v___x_1247_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1245_, v___x_1246_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
return v___x_1247_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_syntheticHole_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1240_ = stack[0].m_obj;
lean_object* v_a_1241_ = stack[1].m_obj;
lean_object* v_a_1242_ = stack[2].m_obj;
lean_object* v_a_1243_ = stack[3].m_obj;
lean_object* v_res_1248_;
v_res_1248_ = l_Lean_Parser_Term_syntheticHole_formatter(v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
stack->m_obj
 = v_res_1248_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter___boxed(lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Parser_Term_syntheticHole_formatter(v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
return v_res_1254_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9(){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1262_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1263_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1264_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0));
v___x_1265_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_formatter___boxed), 5, 0);
v___x_1266_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1262_, v___x_1263_, v___x_1264_, v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1267_;
v_res_1267_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
stack->m_obj
 = v_res_1267_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___boxed(lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
return v_res_1269_;
}
}
lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer(lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0));
v___x_1296_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5));
v___x_1297_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1295_, v___x_1296_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1297_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_syntheticHole_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1290_ = stack[0].m_obj;
lean_object* v_a_1291_ = stack[1].m_obj;
lean_object* v_a_1292_ = stack[2].m_obj;
lean_object* v_a_1293_ = stack[3].m_obj;
lean_object* v_res_1298_;
v_res_1298_ = l_Lean_Parser_Term_syntheticHole_parenthesizer(v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed(lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Parser_Term_syntheticHole_parenthesizer(v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1304_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13(){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1312_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1313_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1314_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0));
v___x_1315_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed), 5, 0);
v___x_1316_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1312_, v___x_1313_, v___x_1314_, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1317_;
v_res_1317_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
stack->m_obj
 = v_res_1317_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___boxed(lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
return v_res_1319_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__2(void){
_start:
{
uint8_t v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1326_ = 0;
v___x_1327_ = 1;
v___x_1328_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1329_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__0));
v___x_1330_ = l_Lean_Parser_mkAntiquot(v___x_1329_, v___x_1328_, v___x_1327_, v___x_1326_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__4(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__3));
v___x_1333_ = l_Lean_Parser_symbol(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__5(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__4, &l_Lean_Parser_Term_omission___closed__4_once, _init_l_Lean_Parser_Term_omission___closed__4);
v___x_1335_ = lean_unsigned_to_nat(1024u);
v___x_1336_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1337_ = l_Lean_Parser_leadingNode(v___x_1336_, v___x_1335_, v___x_1334_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__6(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__5, &l_Lean_Parser_Term_omission___closed__5_once, _init_l_Lean_Parser_Term_omission___closed__5);
v___x_1339_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__2, &l_Lean_Parser_Term_omission___closed__2_once, _init_l_Lean_Parser_Term_omission___closed__2);
v___x_1340_ = l_Lean_Parser_withAntiquot(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__7(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__6, &l_Lean_Parser_Term_omission___closed__6_once, _init_l_Lean_Parser_Term_omission___closed__6);
v___x_1342_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1343_ = l_Lean_Parser_withCache(v___x_1342_, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission(void){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__7, &l_Lean_Parser_Term_omission___closed__7_once, _init_l_Lean_Parser_Term_omission___closed__7);
return v___x_1344_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1(){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1346_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1347_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1348_ = l_Lean_Parser_Term_omission;
v___x_1349_ = lean_unsigned_to_nat(1000u);
v___x_1350_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1346_, v___x_1347_, v___x_1348_, v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1351_;
v_res_1351_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
stack->m_obj
 = v_res_1351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1___boxed(lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
return v_res_1353_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3(){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1357_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0));
v___x_1358_ = l_Lean_addBuiltinDocString(v___x_1356_, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1359_;
v_res_1359_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___boxed(lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
return v_res_1361_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5(){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1389_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6));
v___x_1390_ = l_Lean_addBuiltinDeclarationRanges(v___x_1388_, v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1391_;
v_res_1391_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___boxed(lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
return v_res_1393_;
}
}
lean_object* l_Lean_Parser_Term_omission_formatter(lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__0));
v___x_1413_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__2));
v___x_1414_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1412_, v___x_1413_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
return v___x_1414_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_omission_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1407_ = stack[0].m_obj;
lean_object* v_a_1408_ = stack[1].m_obj;
lean_object* v_a_1409_ = stack[2].m_obj;
lean_object* v_a_1410_ = stack[3].m_obj;
lean_object* v_res_1415_;
v_res_1415_ = l_Lean_Parser_Term_omission_formatter(v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
stack->m_obj
 = v_res_1415_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter___boxed(lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Parser_Term_omission_formatter(v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
return v_res_1421_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9(){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1429_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1430_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1431_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0));
v___x_1432_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_formatter___boxed), 5, 0);
v___x_1433_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1429_, v___x_1430_, v___x_1431_, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1434_;
v_res_1434_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___boxed(lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
return v_res_1436_;
}
}
lean_object* l_Lean_Parser_Term_omission_parenthesizer(lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__0));
v___x_1456_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__2));
v___x_1457_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1455_, v___x_1456_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1457_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_omission_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1450_ = stack[0].m_obj;
lean_object* v_a_1451_ = stack[1].m_obj;
lean_object* v_a_1452_ = stack[2].m_obj;
lean_object* v_a_1453_ = stack[3].m_obj;
lean_object* v_res_1458_;
v_res_1458_ = l_Lean_Parser_Term_omission_parenthesizer(v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
stack->m_obj
 = v_res_1458_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer___boxed(lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Parser_Term_omission_parenthesizer(v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
return v_res_1464_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13(){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1472_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1473_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1474_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0));
v___x_1475_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_parenthesizer___boxed), 5, 0);
v___x_1476_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1472_, v___x_1473_, v___x_1474_, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1477_;
v_res_1477_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
stack->m_obj
 = v_res_1477_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___boxed(lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
return v_res_1479_;
}
}
lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1487_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1485_, v___x_1486_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
return v___x_1487_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderIdent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1480_ = stack[0].m_obj;
lean_object* v_a_1481_ = stack[1].m_obj;
lean_object* v_a_1482_ = stack[2].m_obj;
lean_object* v_a_1483_ = stack[3].m_obj;
lean_object* v_res_1488_;
v_res_1488_ = l_Lean_Parser_Term_binderIdent_formatter(v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
stack->m_obj
 = v_res_1488_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter___boxed(lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Parser_Term_binderIdent_formatter(v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1494_;
}
}
lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_1501_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1502_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_1500_, v___x_1501_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1502_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderIdent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1495_ = stack[0].m_obj;
lean_object* v_a_1496_ = stack[1].m_obj;
lean_object* v_a_1497_ = stack[2].m_obj;
lean_object* v_a_1498_ = stack[3].m_obj;
lean_object* v_res_1503_;
v_res_1503_ = l_Lean_Parser_Term_binderIdent_parenthesizer(v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
stack->m_obj
 = v_res_1503_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer___boxed(lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Parser_Term_binderIdent_parenthesizer(v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1509_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent___closed__0(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = l_Lean_Parser_Term_hole;
v___x_1511_ = l_Lean_Parser_ident;
v___x_1512_ = l_Lean_Parser_orelse(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent(void){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_obj_once(&l_Lean_Parser_Term_binderIdent___closed__0, &l_Lean_Parser_Term_binderIdent___closed__0_once, _init_l_Lean_Parser_Term_binderIdent___closed__0);
return v___x_1513_;
}
}
lean_object* l_Lean_Parser_Term_binderType_formatter(uint8_t v_requireType_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
if (v_requireType_1525_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1532_ = l_Lean_Parser_optional_formatter(v___x_1531_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1534_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1535_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1533_, v___x_1534_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
return v___x_1535_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderType_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_1525_ = stack[0].m_num;
lean_object* v_a_1526_ = stack[1].m_obj;
lean_object* v_a_1527_ = stack[2].m_obj;
lean_object* v_a_1528_ = stack[3].m_obj;
lean_object* v_a_1529_ = stack[4].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_Parser_Term_binderType_formatter(v_requireType_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter___boxed(lean_object* v_requireType_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
uint8_t v_requireType_boxed_1543_; lean_object* v_res_1544_; 
v_requireType_boxed_1543_ = lean_unbox(v_requireType_1537_);
v_res_1544_ = l_Lean_Parser_Term_binderType_formatter(v_requireType_boxed_1543_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
return v_res_1544_;
}
}
lean_object* l_Lean_Parser_Term_binderType_parenthesizer(uint8_t v_requireType_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
if (v_requireType_1552_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1559_ = l_Lean_Parser_optional_parenthesizer(v___x_1558_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1561_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1562_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1560_, v___x_1561_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
return v___x_1562_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderType_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_1552_ = stack[0].m_num;
lean_object* v_a_1553_ = stack[1].m_obj;
lean_object* v_a_1554_ = stack[2].m_obj;
lean_object* v_a_1555_ = stack[3].m_obj;
lean_object* v_a_1556_ = stack[4].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l_Lean_Parser_Term_binderType_parenthesizer(v_requireType_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer___boxed(lean_object* v_requireType_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
uint8_t v_requireType_boxed_1570_; lean_object* v_res_1571_; 
v_requireType_boxed_1570_ = lean_unbox(v_requireType_1564_);
v_res_1571_ = l_Lean_Parser_Term_binderType_parenthesizer(v_requireType_boxed_1570_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1571_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__0(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__0));
v___x_1573_ = l_Lean_Parser_symbol(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = l_Lean_Parser_termParser(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__2(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1577_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1578_ = l_Lean_Parser_andthen(v___x_1577_, v___x_1576_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__3(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1580_ = l_Lean_Parser_optional(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__4(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1582_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1583_ = l_Lean_Parser_node(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
lean_object* l_Lean_Parser_Term_binderType(uint8_t v_requireType_1584_){
_start:
{
if (v_requireType_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__3, &l_Lean_Parser_Term_binderType___closed__3_once, _init_l_Lean_Parser_Term_binderType___closed__3);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__4, &l_Lean_Parser_Term_binderType___closed__4_once, _init_l_Lean_Parser_Term_binderType___closed__4);
return v___x_1586_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderType_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_1584_ = stack[0].m_num;
lean_object* v_res_1587_;
v_res_1587_ = l_Lean_Parser_Term_binderType(v_requireType_1584_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType___boxed(lean_object* v_requireType_1588_){
_start:
{
uint8_t v_requireType_boxed_1589_; lean_object* v_res_1590_; 
v_requireType_boxed_1589_ = lean_unbox(v_requireType_1588_);
v_res_1590_ = l_Lean_Parser_Term_binderType(v_requireType_boxed_1589_);
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_1616_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__8));
v___x_1617_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1617_, 0, v___x_1616_);
lean_closure_set(v___x_1617_, 1, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1618_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__9, &l_Lean_Parser_Term_binderTactic_formatter___closed__9_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9);
v___x_1619_ = lean_unsigned_to_nat(1024u);
v___x_1620_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1621_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1621_, 0, v___x_1620_);
lean_closure_set(v___x_1621_, 1, v___x_1619_);
lean_closure_set(v___x_1621_, 2, v___x_1618_);
return v___x_1621_;
}
}
lean_object* l_Lean_Parser_Term_binderTactic_formatter(lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__2));
v___x_1628_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__10, &l_Lean_Parser_Term_binderTactic_formatter___closed__10_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10);
v___x_1629_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1627_, v___x_1628_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
return v___x_1629_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderTactic_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1622_ = stack[0].m_obj;
lean_object* v_a_1623_ = stack[1].m_obj;
lean_object* v_a_1624_ = stack[2].m_obj;
lean_object* v_a_1625_ = stack[3].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Lean_Parser_Term_binderTactic_formatter(v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter___boxed(lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Parser_Term_binderTactic_formatter(v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1636_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3(){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1644_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1645_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1646_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0));
v___x_1647_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_1648_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1644_, v___x_1645_, v___x_1646_, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1649_;
v_res_1649_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
stack->m_obj
 = v_res_1649_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___boxed(lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
return v_res_1651_;
}
}
lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_1652_, v___x_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1652_ = stack[0].m_obj;
lean_object* v___x_1653_ = stack[1].m_obj;
lean_object* v___y_1654_ = stack[2].m_obj;
lean_object* v___y_1655_ = stack[3].m_obj;
lean_object* v___y_1656_ = stack[4].m_obj;
lean_object* v___y_1657_ = stack[5].m_obj;
lean_object* v_res_1660_;
v_res_1660_ = l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(v___x_1652_, v___x_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
stack->m_obj
 = v_res_1660_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed(lean_object* v___x_1661_, lean_object* v___x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(v___x_1661_, v___x_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___f_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___f_1684_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3));
v___x_1685_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1685_, 0, v___f_1684_);
lean_closure_set(v___x_1685_, 1, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1686_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4);
v___x_1687_ = lean_unsigned_to_nat(1024u);
v___x_1688_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1689_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1689_, 0, v___x_1688_);
lean_closure_set(v___x_1689_, 1, v___x_1687_);
lean_closure_set(v___x_1689_, 2, v___x_1686_);
return v___x_1689_;
}
}
lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer(lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0));
v___x_1696_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5);
v___x_1697_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1695_, v___x_1696_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1697_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderTactic_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1690_ = stack[0].m_obj;
lean_object* v_a_1691_ = stack[1].m_obj;
lean_object* v_a_1692_ = stack[2].m_obj;
lean_object* v_a_1693_ = stack[3].m_obj;
lean_object* v_res_1698_;
v_res_1698_ = l_Lean_Parser_Term_binderTactic_parenthesizer(v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
stack->m_obj
 = v_res_1698_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___boxed(lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Parser_Term_binderTactic_parenthesizer(v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1704_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7(){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1712_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1713_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1714_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0));
v___x_1715_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_1716_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1712_, v___x_1713_, v___x_1714_, v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1717_;
v_res_1717_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___boxed(lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
return v_res_1719_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__0(void){
_start:
{
uint8_t v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1720_ = 0;
v___x_1721_ = 1;
v___x_1722_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1723_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__0));
v___x_1724_ = l_Lean_Parser_mkAntiquot(v___x_1723_, v___x_1722_, v___x_1721_, v___x_1720_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__1(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__3));
v___x_1726_ = l_Lean_Parser_symbol(v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__2(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__5));
v___x_1728_ = l_Lean_Parser_symbol(v___x_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__3(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__2, &l_Lean_Parser_Term_binderTactic___closed__2_once, _init_l_Lean_Parser_Term_binderTactic___closed__2);
v___x_1730_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1731_ = l_Lean_Parser_andthen(v___x_1730_, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__4(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__3, &l_Lean_Parser_Term_binderTactic___closed__3_once, _init_l_Lean_Parser_Term_binderTactic___closed__3);
v___x_1733_ = l_Lean_Parser_atomic(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__5(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_1735_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__4, &l_Lean_Parser_Term_binderTactic___closed__4_once, _init_l_Lean_Parser_Term_binderTactic___closed__4);
v___x_1736_ = l_Lean_Parser_andthen(v___x_1735_, v___x_1734_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__6(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__5, &l_Lean_Parser_Term_binderTactic___closed__5_once, _init_l_Lean_Parser_Term_binderTactic___closed__5);
v___x_1738_ = lean_unsigned_to_nat(1024u);
v___x_1739_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1740_ = l_Lean_Parser_leadingNode(v___x_1739_, v___x_1738_, v___x_1737_);
return v___x_1740_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__7(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__6, &l_Lean_Parser_Term_binderTactic___closed__6_once, _init_l_Lean_Parser_Term_binderTactic___closed__6);
v___x_1742_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__0, &l_Lean_Parser_Term_binderTactic___closed__0_once, _init_l_Lean_Parser_Term_binderTactic___closed__0);
v___x_1743_ = l_Lean_Parser_withAntiquot(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__8(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__7, &l_Lean_Parser_Term_binderTactic___closed__7_once, _init_l_Lean_Parser_Term_binderTactic___closed__7);
v___x_1745_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1746_ = l_Lean_Parser_withCache(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic(void){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__8, &l_Lean_Parser_Term_binderTactic___closed__8_once, _init_l_Lean_Parser_Term_binderTactic___closed__8);
return v___x_1747_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__2(void){
_start:
{
uint8_t v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1754_ = 0;
v___x_1755_ = 1;
v___x_1756_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1757_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__0));
v___x_1758_ = l_Lean_Parser_mkAntiquot(v___x_1757_, v___x_1756_, v___x_1755_, v___x_1754_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__3(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1760_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1761_ = l_Lean_Parser_andthen(v___x_1760_, v___x_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__4(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__3, &l_Lean_Parser_Term_binderDefault___closed__3_once, _init_l_Lean_Parser_Term_binderDefault___closed__3);
v___x_1763_ = lean_unsigned_to_nat(1024u);
v___x_1764_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1765_ = l_Lean_Parser_leadingNode(v___x_1764_, v___x_1763_, v___x_1762_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__5(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__4, &l_Lean_Parser_Term_binderDefault___closed__4_once, _init_l_Lean_Parser_Term_binderDefault___closed__4);
v___x_1767_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__2, &l_Lean_Parser_Term_binderDefault___closed__2_once, _init_l_Lean_Parser_Term_binderDefault___closed__2);
v___x_1768_ = l_Lean_Parser_withAntiquot(v___x_1767_, v___x_1766_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__6(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__5, &l_Lean_Parser_Term_binderDefault___closed__5_once, _init_l_Lean_Parser_Term_binderDefault___closed__5);
v___x_1770_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1771_ = l_Lean_Parser_withCache(v___x_1770_, v___x_1769_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault(void){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__6, &l_Lean_Parser_Term_binderDefault___closed__6_once, _init_l_Lean_Parser_Term_binderDefault___closed__6);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM(void){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Parser_Term_binderDefault;
return v___x_1773_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; lean_object* v_stxTrav_1777_; lean_object* v_cur_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_st_ref_get(v___y_1774_);
v_stxTrav_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_stxTrav_1777_);
lean_dec(v___x_1776_);
v_cur_1778_ = lean_ctor_get(v_stxTrav_1777_, 0);
lean_inc(v_cur_1778_);
lean_dec_ref(v_stxTrav_1777_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_cur_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1774_ = stack[0].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1774_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1781_);
lean_dec(v___y_1781_);
return v_res_1783_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1785_);
return v___x_1789_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1784_ = stack[0].m_obj;
lean_object* v___y_1785_ = stack[1].m_obj;
lean_object* v___y_1786_ = stack[2].m_obj;
lean_object* v___y_1787_ = stack[3].m_obj;
lean_object* v_res_1790_;
v_res_1790_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
stack->m_obj
 = v_res_1790_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___boxed(lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v___x_1803_, 1);
v___x_1804_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_1799_);
return v___x_1804_;
}
else
{
return v___x_1803_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1797_ = stack[0].m_obj;
lean_object* v___y_1798_ = stack[1].m_obj;
lean_object* v___y_1799_ = stack[2].m_obj;
lean_object* v___y_1800_ = stack[3].m_obj;
lean_object* v___y_1801_ = stack[4].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed(lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer(lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v_a_1825_; lean_object* v___y_1827_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1824_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v_a_1820_);
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc_n(v_a_1825_, 2);
lean_dec_ref(v___x_1824_);
v___x_1830_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1831_ = l_Lean_Syntax_isOfKind(v_a_1825_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec(v_a_1825_);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___y_1827_ = v___x_1832_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1833_ = lean_unsigned_to_nat(1u);
v___x_1834_ = l_Lean_Syntax_getArg(v_a_1825_, v___x_1833_);
lean_dec(v_a_1825_);
v___x_1835_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1));
v___x_1836_ = l_Lean_Syntax_isOfKind(v___x_1834_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___y_1827_ = v___x_1837_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Parser_maxPrec;
v___y_1827_ = v___x_1838_;
goto v___jp_1826_;
}
}
v___jp_1826_:
{
lean_object* v___f_1828_; lean_object* v___x_1829_; 
v___f_1828_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1828_, 0, v___y_1827_);
v___x_1829_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___f_1828_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
return v___x_1829_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderDefault_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1819_ = stack[0].m_obj;
lean_object* v_a_1820_ = stack[1].m_obj;
lean_object* v_a_1821_ = stack[2].m_obj;
lean_object* v_a_1822_ = stack[3].m_obj;
lean_object* v_res_1839_;
v_res_1839_ = l_Lean_Parser_Term_binderDefault_parenthesizer(v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
stack->m_obj
 = v_res_1839_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___boxed(lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Parser_Term_binderDefault_parenthesizer(v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1845_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1852_ = 0;
v___x_1853_ = 1;
v___x_1854_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1855_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__0));
v___x_1856_ = l_Lean_Parser_mkAntiquot(v___x_1855_, v___x_1854_, v___x_1853_, v___x_1852_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__3));
v___x_1859_ = l_Lean_Parser_symbol(v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__5(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = l_Lean_Parser_Term_binderIdent;
v___x_1861_ = l_Lean_Parser_many1(v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__6(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = l_Lean_Parser_Term_binderDefault;
v___x_1863_ = l_Lean_Parser_Term_binderTactic;
v___x_1864_ = l_Lean_Parser_orelse(v___x_1863_, v___x_1862_);
return v___x_1864_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__7(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__6, &l_Lean_Parser_Term_explicitBinder___closed__6_once, _init_l_Lean_Parser_Term_explicitBinder___closed__6);
v___x_1866_ = l_Lean_Parser_optional(v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__9(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__8));
v___x_1869_ = l_Lean_Parser_symbol(v___x_1868_);
return v___x_1869_;
}
}
lean_object* l_Lean_Parser_Term_explicitBinder(uint8_t v_requireType_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1871_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1872_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__2, &l_Lean_Parser_Term_explicitBinder___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder___closed__2);
v___x_1873_ = lean_unsigned_to_nat(1024u);
v___x_1874_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__4, &l_Lean_Parser_Term_explicitBinder___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder___closed__4);
v___x_1875_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1876_ = l_Lean_Parser_Term_binderType(v_requireType_1870_);
v___x_1877_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__7, &l_Lean_Parser_Term_explicitBinder___closed__7_once, _init_l_Lean_Parser_Term_explicitBinder___closed__7);
v___x_1878_ = l_Lean_Parser_andthen(v___x_1876_, v___x_1877_);
v___x_1879_ = l_Lean_Parser_andthen(v___x_1875_, v___x_1878_);
v___x_1880_ = l_Lean_Parser_withoutPosition(v___x_1879_);
v___x_1881_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__9, &l_Lean_Parser_Term_explicitBinder___closed__9_once, _init_l_Lean_Parser_Term_explicitBinder___closed__9);
v___x_1882_ = l_Lean_Parser_andthen(v___x_1880_, v___x_1881_);
v___x_1883_ = l_Lean_Parser_andthen(v___x_1874_, v___x_1882_);
v___x_1884_ = l_Lean_Parser_leadingNode(v___x_1871_, v___x_1873_, v___x_1883_);
v___x_1885_ = l_Lean_Parser_withAntiquot(v___x_1872_, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_explicitBinder_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_1870_ = stack[0].m_num;
lean_object* v_res_1886_;
v_res_1886_ = l_Lean_Parser_Term_explicitBinder(v_requireType_1870_);
stack->m_obj
 = v_res_1886_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___boxed(lean_object* v_requireType_1887_){
_start:
{
uint8_t v_requireType_boxed_1888_; lean_object* v_res_1889_; 
v_requireType_boxed_1888_ = lean_unbox(v_requireType_1887_);
v_res_1889_ = l_Lean_Parser_Term_explicitBinder(v_requireType_boxed_1888_);
return v_res_1889_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1(){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1893_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0));
v___x_1894_ = l_Lean_addBuiltinDocString(v___x_1892_, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1895_;
v_res_1895_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___boxed(lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
return v_res_1897_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1904_ = 0;
v___x_1905_ = 1;
v___x_1906_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1907_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__0));
v___x_1908_ = l_Lean_Parser_mkAntiquot(v___x_1907_, v___x_1906_, v___x_1905_, v___x_1904_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__3));
v___x_1911_ = l_Lean_Parser_symbol(v___x_1910_);
return v___x_1911_;
}
}
lean_object* l_Lean_Parser_Term_implicitBinder(uint8_t v_requireType_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1913_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1914_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__2, &l_Lean_Parser_Term_implicitBinder___closed__2_once, _init_l_Lean_Parser_Term_implicitBinder___closed__2);
v___x_1915_ = lean_unsigned_to_nat(1024u);
v___x_1916_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1917_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1918_ = l_Lean_Parser_Term_binderType(v_requireType_1912_);
v___x_1919_ = l_Lean_Parser_andthen(v___x_1917_, v___x_1918_);
v___x_1920_ = l_Lean_Parser_withoutPosition(v___x_1919_);
v___x_1921_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1922_ = l_Lean_Parser_andthen(v___x_1920_, v___x_1921_);
v___x_1923_ = l_Lean_Parser_andthen(v___x_1916_, v___x_1922_);
v___x_1924_ = l_Lean_Parser_leadingNode(v___x_1913_, v___x_1915_, v___x_1923_);
v___x_1925_ = l_Lean_Parser_withAntiquot(v___x_1914_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_implicitBinder_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_1912_ = stack[0].m_num;
lean_object* v_res_1926_;
v_res_1926_ = l_Lean_Parser_Term_implicitBinder(v_requireType_1912_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___boxed(lean_object* v_requireType_1927_){
_start:
{
uint8_t v_requireType_boxed_1928_; lean_object* v_res_1929_; 
v_requireType_boxed_1928_ = lean_unbox(v_requireType_1927_);
v_res_1929_ = l_Lean_Parser_Term_implicitBinder(v_requireType_boxed_1928_);
return v_res_1929_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1(){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1933_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0));
v___x_1934_ = l_Lean_addBuiltinDocString(v___x_1932_, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1935_;
v_res_1935_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
stack->m_obj
 = v_res_1935_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___boxed(lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
return v_res_1937_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1939_ = l_Lean_Parser_andthen(v___x_1938_, v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0);
v___x_1944_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1945_ = l_Lean_Parser_node(v___x_1944_, v___x_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3);
v___x_1947_ = l_Lean_Parser_atomic(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5));
v___x_1950_ = l_Lean_Parser_symbol(v___x_1949_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6);
v___x_1952_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4);
v___x_1953_ = l_Lean_Parser_orelse(v___x_1952_, v___x_1951_);
return v___x_1953_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket(void){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1956_ = l_Lean_Parser_andthen(v___x_1955_, v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__0, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0);
v___x_1958_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1959_ = l_Lean_Parser_node(v___x_1958_, v___x_1957_);
return v___x_1959_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__1, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1);
v___x_1961_ = l_Lean_Parser_atomic(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket___closed__3));
v___x_1964_ = l_Lean_Parser_symbol(v___x_1963_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__4, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4);
v___x_1966_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__2, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2);
v___x_1967_ = l_Lean_Parser_orelse(v___x_1966_, v___x_1965_);
return v___x_1967_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket(void){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__5, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__5_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1975_ = 0;
v___x_1976_ = 1;
v___x_1977_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1978_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__0));
v___x_1979_ = l_Lean_Parser_mkAntiquot(v___x_1978_, v___x_1977_, v___x_1976_, v___x_1975_);
return v___x_1979_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitBinder(uint8_t v_requireType_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1981_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1982_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitBinder___closed__2, &l_Lean_Parser_Term_strictImplicitBinder___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2);
v___x_1983_ = lean_unsigned_to_nat(1024u);
v___x_1984_ = l_Lean_Parser_Term_strictImplicitLeftBracket;
v___x_1985_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1986_ = l_Lean_Parser_Term_binderType(v_requireType_1980_);
v___x_1987_ = l_Lean_Parser_Term_strictImplicitRightBracket;
v___x_1988_ = l_Lean_Parser_andthen(v___x_1986_, v___x_1987_);
v___x_1989_ = l_Lean_Parser_andthen(v___x_1985_, v___x_1988_);
v___x_1990_ = l_Lean_Parser_andthen(v___x_1984_, v___x_1989_);
v___x_1991_ = l_Lean_Parser_leadingNode(v___x_1981_, v___x_1983_, v___x_1990_);
v___x_1992_ = l_Lean_Parser_withAntiquot(v___x_1982_, v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitBinder_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_1980_ = stack[0].m_num;
lean_object* v_res_1993_;
v_res_1993_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_1980_);
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___boxed(lean_object* v_requireType_1994_){
_start:
{
uint8_t v_requireType_boxed_1995_; lean_object* v_res_1996_; 
v_requireType_boxed_1995_ = lean_unbox(v_requireType_1994_);
v_res_1996_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_boxed_1995_);
return v_res_1996_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1(){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2000_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0));
v___x_2001_ = l_Lean_addBuiltinDocString(v___x_1999_, v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2002_;
v_res_2002_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
stack->m_obj
 = v_res_2002_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___boxed(lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
return v_res_2004_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__0(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_2006_ = l_Lean_Parser_ident;
v___x_2007_ = l_Lean_Parser_andthen(v___x_2006_, v___x_2005_);
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__1(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__0, &l_Lean_Parser_Term_optIdent___closed__0_once, _init_l_Lean_Parser_Term_optIdent___closed__0);
v___x_2009_ = l_Lean_Parser_atomic(v___x_2008_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__2(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__1, &l_Lean_Parser_Term_optIdent___closed__1_once, _init_l_Lean_Parser_Term_optIdent___closed__1);
v___x_2011_ = l_Lean_Parser_optional(v___x_2010_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent(void){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__2, &l_Lean_Parser_Term_optIdent___closed__2_once, _init_l_Lean_Parser_Term_optIdent___closed__2);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__2(void){
_start:
{
uint8_t v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2019_ = 0;
v___x_2020_ = 1;
v___x_2021_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2022_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__0));
v___x_2023_ = l_Lean_Parser_mkAntiquot(v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__4(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__3));
v___x_2026_ = l_Lean_Parser_symbol(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__5(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_2028_ = l_Lean_Parser_Term_optIdent;
v___x_2029_ = l_Lean_Parser_andthen(v___x_2028_, v___x_2027_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__6(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__5, &l_Lean_Parser_Term_instBinder___closed__5_once, _init_l_Lean_Parser_Term_instBinder___closed__5);
v___x_2031_ = l_Lean_Parser_withoutPosition(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__8(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__7));
v___x_2034_ = l_Lean_Parser_symbol(v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__9(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_2036_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__6, &l_Lean_Parser_Term_instBinder___closed__6_once, _init_l_Lean_Parser_Term_instBinder___closed__6);
v___x_2037_ = l_Lean_Parser_andthen(v___x_2036_, v___x_2035_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__10(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__9, &l_Lean_Parser_Term_instBinder___closed__9_once, _init_l_Lean_Parser_Term_instBinder___closed__9);
v___x_2039_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_2040_ = l_Lean_Parser_andthen(v___x_2039_, v___x_2038_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__11(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__10, &l_Lean_Parser_Term_instBinder___closed__10_once, _init_l_Lean_Parser_Term_instBinder___closed__10);
v___x_2042_ = lean_unsigned_to_nat(1024u);
v___x_2043_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2044_ = l_Lean_Parser_leadingNode(v___x_2043_, v___x_2042_, v___x_2041_);
return v___x_2044_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__12(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__11, &l_Lean_Parser_Term_instBinder___closed__11_once, _init_l_Lean_Parser_Term_instBinder___closed__11);
v___x_2046_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__2, &l_Lean_Parser_Term_instBinder___closed__2_once, _init_l_Lean_Parser_Term_instBinder___closed__2);
v___x_2047_ = l_Lean_Parser_withAntiquot(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__13(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__12, &l_Lean_Parser_Term_instBinder___closed__12_once, _init_l_Lean_Parser_Term_instBinder___closed__12);
v___x_2049_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2050_ = l_Lean_Parser_withCache(v___x_2049_, v___x_2048_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder(void){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__13, &l_Lean_Parser_Term_instBinder___closed__13_once, _init_l_Lean_Parser_Term_instBinder___closed__13);
return v___x_2051_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1(){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2055_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0));
v___x_2056_ = l_Lean_addBuiltinDocString(v___x_2054_, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2057_;
v_res_2057_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
stack->m_obj
 = v_res_2057_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___boxed(lean_object* v_a_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
return v_res_2059_;
}
}
lean_object* l_Lean_Parser_Term_binderDefault_formatter(lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__0));
v___x_2080_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__2));
v___x_2081_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2079_, v___x_2080_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2081_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_binderDefault_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2074_ = stack[0].m_obj;
lean_object* v_a_2075_ = stack[1].m_obj;
lean_object* v_a_2076_ = stack[2].m_obj;
lean_object* v_a_2077_ = stack[3].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l_Lean_Parser_Term_binderDefault_formatter(v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter___boxed(lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_Parser_Term_binderDefault_formatter(v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
return v_res_2088_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3(){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2096_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2097_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_2098_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0));
v___x_2099_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2100_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2096_, v___x_2097_, v___x_2098_, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2101_;
v_res_2101_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
stack->m_obj
 = v_res_2101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___boxed(lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
return v_res_2103_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_2114_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter___boxed), 6, 1);
lean_closure_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2116_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2117_, 0, v___x_2116_);
lean_closure_set(v___x_2117_, 1, v___x_2115_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__3, &l_Lean_Parser_Term_explicitBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3);
v___x_2119_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
lean_object* l_Lean_Parser_Term_explicitBinder_formatter(uint8_t v_requireType_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2128_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2129_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__0));
v___x_2130_ = lean_unsigned_to_nat(1024u);
v___x_2131_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__1));
v___x_2132_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2133_ = lean_box(v_requireType_2122_);
v___x_2134_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__4, &l_Lean_Parser_Term_explicitBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4);
v___x_2136_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2136_, 0, v___x_2134_);
lean_closure_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2137_, 0, v___x_2132_);
lean_closure_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2138_, 0, v___x_2137_);
v___x_2139_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__5));
v___x_2140_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2140_, 0, v___x_2138_);
lean_closure_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2141_, 0, v___x_2131_);
lean_closure_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2142_, 0, v___x_2141_);
v___x_2143_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2143_, 0, v___x_2128_);
lean_closure_set(v___x_2143_, 1, v___x_2130_);
lean_closure_set(v___x_2143_, 2, v___x_2142_);
v___x_2144_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2129_, v___x_2143_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2144_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_explicitBinder_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2122_ = stack[0].m_num;
lean_object* v_a_2123_ = stack[1].m_obj;
lean_object* v_a_2124_ = stack[2].m_obj;
lean_object* v_a_2125_ = stack[3].m_obj;
lean_object* v_a_2126_ = stack[4].m_obj;
lean_object* v_res_2145_;
v_res_2145_ = l_Lean_Parser_Term_explicitBinder_formatter(v_requireType_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
stack->m_obj
 = v_res_2145_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter___boxed(lean_object* v_requireType_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
uint8_t v_requireType_boxed_2152_; lean_object* v_res_2153_; 
v_requireType_boxed_2152_ = lean_unbox(v_requireType_2146_);
v_res_2153_ = l_Lean_Parser_Term_explicitBinder_formatter(v_requireType_boxed_2152_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2153_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3));
v___x_2170_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4));
v___x_2171_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2169_, v___x_2170_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2171_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitLeftBracket_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2164_ = stack[0].m_obj;
lean_object* v_a_2165_ = stack[1].m_obj;
lean_object* v_a_2166_ = stack[2].m_obj;
lean_object* v_a_2167_ = stack[3].m_obj;
lean_object* v_res_2172_;
v_res_2172_ = l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
stack->m_obj
 = v_res_2172_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed(lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
return v_res_2178_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter(lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2));
v___x_2193_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3));
v___x_2194_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2192_, v___x_2193_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2194_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitRightBracket_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2187_ = stack[0].m_obj;
lean_object* v_a_2188_ = stack[1].m_obj;
lean_object* v_a_2189_ = stack[2].m_obj;
lean_object* v_a_2190_ = stack[3].m_obj;
lean_object* v_res_2195_;
v_res_2195_ = l_Lean_Parser_Term_strictImplicitRightBracket_formatter(v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed(lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Parser_Term_strictImplicitRightBracket_formatter(v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
return v_res_2201_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter(uint8_t v_requireType_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2215_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2216_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0));
v___x_2217_ = lean_unsigned_to_nat(1024u);
v___x_2218_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed), 5, 0);
v___x_2219_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2220_ = lean_box(v_requireType_2209_);
v___x_2221_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2221_, 0, v___x_2220_);
v___x_2222_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed), 5, 0);
v___x_2223_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2223_, 0, v___x_2221_);
lean_closure_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2224_, 0, v___x_2219_);
lean_closure_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2225_, 0, v___x_2218_);
lean_closure_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2226_, 0, v___x_2225_);
v___x_2227_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2227_, 0, v___x_2215_);
lean_closure_set(v___x_2227_, 1, v___x_2217_);
lean_closure_set(v___x_2227_, 2, v___x_2226_);
v___x_2228_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2216_, v___x_2227_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v___x_2228_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitBinder_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2209_ = stack[0].m_num;
lean_object* v_a_2210_ = stack[1].m_obj;
lean_object* v_a_2211_ = stack[2].m_obj;
lean_object* v_a_2212_ = stack[3].m_obj;
lean_object* v_a_2213_ = stack[4].m_obj;
lean_object* v_res_2229_;
v_res_2229_ = l_Lean_Parser_Term_strictImplicitBinder_formatter(v_requireType_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
stack->m_obj
 = v_res_2229_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed(lean_object* v_requireType_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
uint8_t v_requireType_boxed_2236_; lean_object* v_res_2237_; 
v_requireType_boxed_2236_ = lean_unbox(v_requireType_2230_);
v_res_2237_ = l_Lean_Parser_Term_strictImplicitBinder_formatter(v_requireType_boxed_2236_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2237_;
}
}
lean_object* l_Lean_Parser_Term_implicitBinder_formatter(uint8_t v_requireType_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2251_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2252_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_formatter___closed__0));
v___x_2253_ = lean_unsigned_to_nat(1024u);
v___x_2254_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0));
v___x_2255_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2256_ = lean_box(v_requireType_2245_);
v___x_2257_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2257_, 0, v___x_2256_);
v___x_2258_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2258_, 0, v___x_2255_);
lean_closure_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2259_, 0, v___x_2258_);
v___x_2260_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_2261_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2261_, 0, v___x_2259_);
lean_closure_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2262_, 0, v___x_2254_);
lean_closure_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2264_, 0, v___x_2251_);
lean_closure_set(v___x_2264_, 1, v___x_2253_);
lean_closure_set(v___x_2264_, 2, v___x_2263_);
v___x_2265_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2252_, v___x_2264_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
return v___x_2265_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_implicitBinder_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2245_ = stack[0].m_num;
lean_object* v_a_2246_ = stack[1].m_obj;
lean_object* v_a_2247_ = stack[2].m_obj;
lean_object* v_a_2248_ = stack[3].m_obj;
lean_object* v_a_2249_ = stack[4].m_obj;
lean_object* v_res_2266_;
v_res_2266_ = l_Lean_Parser_Term_implicitBinder_formatter(v_requireType_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
stack->m_obj
 = v_res_2266_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter___boxed(lean_object* v_requireType_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
uint8_t v_requireType_boxed_2273_; lean_object* v_res_2274_; 
v_requireType_boxed_2273_ = lean_unbox(v_requireType_2267_);
v_res_2274_ = l_Lean_Parser_Term_implicitBinder_formatter(v_requireType_boxed_2273_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
return v_res_2274_;
}
}
lean_object* l_Lean_Parser_Term_optIdent_formatter(lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_formatter___closed__1));
v___x_2286_ = l_Lean_Parser_optional_formatter(v___x_2285_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2286_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optIdent_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2280_ = stack[0].m_obj;
lean_object* v_a_2281_ = stack[1].m_obj;
lean_object* v_a_2282_ = stack[2].m_obj;
lean_object* v_a_2283_ = stack[3].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l_Lean_Parser_Term_optIdent_formatter(v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter___boxed(lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Parser_Term_optIdent_formatter(v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2293_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__2));
v___x_2304_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_formatter___boxed), 5, 0);
v___x_2305_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2305_, 0, v___x_2304_);
lean_closure_set(v___x_2305_, 1, v___x_2303_);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__2, &l_Lean_Parser_Term_instBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__2);
v___x_2307_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__5(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__4));
v___x_2311_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__3, &l_Lean_Parser_Term_instBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__3);
v___x_2312_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2312_, 0, v___x_2311_);
lean_closure_set(v___x_2312_, 1, v___x_2310_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__6(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__5, &l_Lean_Parser_Term_instBinder_formatter___closed__5_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__5);
v___x_2314_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__1));
v___x_2315_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2315_, 0, v___x_2314_);
lean_closure_set(v___x_2315_, 1, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__7(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__6, &l_Lean_Parser_Term_instBinder_formatter___closed__6_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__6);
v___x_2317_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__8(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__7, &l_Lean_Parser_Term_instBinder_formatter___closed__7_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__7);
v___x_2319_ = lean_unsigned_to_nat(1024u);
v___x_2320_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2321_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2321_, 0, v___x_2320_);
lean_closure_set(v___x_2321_, 1, v___x_2319_);
lean_closure_set(v___x_2321_, 2, v___x_2318_);
return v___x_2321_;
}
}
lean_object* l_Lean_Parser_Term_instBinder_formatter(lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__0));
v___x_2328_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__8, &l_Lean_Parser_Term_instBinder_formatter___closed__8_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__8);
v___x_2329_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2327_, v___x_2328_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
return v___x_2329_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_instBinder_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2322_ = stack[0].m_obj;
lean_object* v_a_2323_ = stack[1].m_obj;
lean_object* v_a_2324_ = stack[2].m_obj;
lean_object* v_a_2325_ = stack[3].m_obj;
lean_object* v_res_2330_;
v_res_2330_ = l_Lean_Parser_Term_instBinder_formatter(v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
stack->m_obj
 = v_res_2330_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter___boxed(lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_Parser_Term_instBinder_formatter(v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
return v_res_2336_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19(){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2344_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2345_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2346_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0));
v___x_2347_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2348_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2349_;
v_res_2349_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
stack->m_obj
 = v_res_2349_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___boxed(lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
return v_res_2351_;
}
}
lean_object* l_Lean_Parser_Term_bracketedBinder_formatter(uint8_t v_requireType_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2370_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__2));
v___x_2371_ = lean_box(v_requireType_2364_);
v___x_2372_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2372_, 0, v___x_2371_);
v___x_2373_ = lean_box(v_requireType_2364_);
v___x_2374_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2374_, 0, v___x_2373_);
v___x_2375_ = lean_box(v_requireType_2364_);
v___x_2376_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2378_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2378_, 0, v___x_2376_);
lean_closure_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2379_, 0, v___x_2374_);
lean_closure_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2380_, 0, v___x_2372_);
lean_closure_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2370_, v___x_2380_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2381_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_bracketedBinder_formatter_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2364_ = stack[0].m_num;
lean_object* v_a_2365_ = stack[1].m_obj;
lean_object* v_a_2366_ = stack[2].m_obj;
lean_object* v_a_2367_ = stack[3].m_obj;
lean_object* v_a_2368_ = stack[4].m_obj;
lean_object* v_res_2382_;
v_res_2382_ = l_Lean_Parser_Term_bracketedBinder_formatter(v_requireType_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
stack->m_obj
 = v_res_2382_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object* v_requireType_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
uint8_t v_requireType_boxed_2389_; lean_object* v_res_2390_; 
v_requireType_boxed_2389_ = lean_unbox(v_requireType_2383_);
v_res_2390_ = l_Lean_Parser_Term_bracketedBinder_formatter(v_requireType_boxed_2389_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2390_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_2401_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___boxed), 5, 0);
v___x_2403_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_2404_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2404_, 0, v___x_2403_);
lean_closure_set(v___x_2404_, 1, v___x_2402_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3);
v___x_2406_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer(uint8_t v_requireType_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2415_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2416_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0));
v___x_2417_ = lean_unsigned_to_nat(1024u);
v___x_2418_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1));
v___x_2419_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2420_ = lean_box(v_requireType_2409_);
v___x_2421_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2421_, 0, v___x_2420_);
v___x_2422_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4);
v___x_2423_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2423_, 0, v___x_2421_);
lean_closure_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2424_, 0, v___x_2419_);
lean_closure_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2425_, 0, v___x_2424_);
v___x_2426_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5));
v___x_2427_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2427_, 0, v___x_2425_);
lean_closure_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2428_, 0, v___x_2418_);
lean_closure_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2429_, 0, v___x_2428_);
v___x_2430_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2430_, 0, v___x_2415_);
lean_closure_set(v___x_2430_, 1, v___x_2417_);
lean_closure_set(v___x_2430_, 2, v___x_2429_);
v___x_2431_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2416_, v___x_2430_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2431_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_explicitBinder_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2409_ = stack[0].m_num;
lean_object* v_a_2410_ = stack[1].m_obj;
lean_object* v_a_2411_ = stack[2].m_obj;
lean_object* v_a_2412_ = stack[3].m_obj;
lean_object* v_a_2413_ = stack[4].m_obj;
lean_object* v_res_2432_;
v_res_2432_ = l_Lean_Parser_Term_explicitBinder_parenthesizer(v_requireType_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
stack->m_obj
 = v_res_2432_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed(lean_object* v_requireType_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_requireType_boxed_2439_; lean_object* v_res_2440_; 
v_requireType_boxed_2439_ = lean_unbox(v_requireType_2433_);
v_res_2440_ = l_Lean_Parser_Term_explicitBinder_parenthesizer(v_requireType_boxed_2439_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2440_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(lean_object* v___x_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Parser_group_parenthesizer(v___x_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
return v___x_2447_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2441_ = stack[0].m_obj;
lean_object* v___y_2442_ = stack[1].m_obj;
lean_object* v___y_2443_ = stack[2].m_obj;
lean_object* v___y_2444_ = stack[3].m_obj;
lean_object* v___y_2445_ = stack[4].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(v___x_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed(lean_object* v___x_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(v___x_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2455_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___f_2469_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2));
v___x_2470_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3));
v___x_2471_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2469_, v___x_2470_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
return v___x_2471_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2464_ = stack[0].m_obj;
lean_object* v_a_2465_ = stack[1].m_obj;
lean_object* v_a_2466_ = stack[2].m_obj;
lean_object* v_a_2467_ = stack[3].m_obj;
lean_object* v_res_2472_;
v_res_2472_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
stack->m_obj
 = v_res_2472_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed(lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2478_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___f_2490_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1));
v___x_2491_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2));
v___x_2492_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2490_, v___x_2491_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
return v___x_2492_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2485_ = stack[0].m_obj;
lean_object* v_a_2486_ = stack[1].m_obj;
lean_object* v_a_2487_ = stack[2].m_obj;
lean_object* v_a_2488_ = stack[3].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed(lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
return v_res_2499_;
}
}
lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(uint8_t v_requireType_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2513_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2514_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0));
v___x_2515_ = lean_unsigned_to_nat(1024u);
v___x_2516_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed), 5, 0);
v___x_2517_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2518_ = lean_box(v_requireType_2507_);
v___x_2519_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2519_, 0, v___x_2518_);
v___x_2520_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed), 5, 0);
v___x_2521_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2521_, 0, v___x_2519_);
lean_closure_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2522_, 0, v___x_2517_);
lean_closure_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2523_, 0, v___x_2516_);
lean_closure_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2524_, 0, v___x_2523_);
v___x_2525_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2525_, 0, v___x_2513_);
lean_closure_set(v___x_2525_, 1, v___x_2515_);
lean_closure_set(v___x_2525_, 2, v___x_2524_);
v___x_2526_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2514_, v___x_2525_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2526_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_strictImplicitBinder_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2507_ = stack[0].m_num;
lean_object* v_a_2508_ = stack[1].m_obj;
lean_object* v_a_2509_ = stack[2].m_obj;
lean_object* v_a_2510_ = stack[3].m_obj;
lean_object* v_a_2511_ = stack[4].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(v_requireType_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
stack->m_obj
 = v_res_2527_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed(lean_object* v_requireType_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
uint8_t v_requireType_boxed_2534_; lean_object* v_res_2535_; 
v_requireType_boxed_2534_ = lean_unbox(v_requireType_2528_);
v_res_2535_ = l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(v_requireType_boxed_2534_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
return v_res_2535_;
}
}
lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer(uint8_t v_requireType_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2549_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2550_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0));
v___x_2551_ = lean_unsigned_to_nat(1024u);
v___x_2552_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0));
v___x_2553_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2554_ = lean_box(v_requireType_2543_);
v___x_2555_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2555_, 0, v___x_2554_);
v___x_2556_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2556_, 0, v___x_2553_);
lean_closure_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2557_, 0, v___x_2556_);
v___x_2558_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6));
v___x_2559_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2559_, 0, v___x_2557_);
lean_closure_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2560_, 0, v___x_2552_);
lean_closure_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2561_, 0, v___x_2560_);
v___x_2562_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2562_, 0, v___x_2549_);
lean_closure_set(v___x_2562_, 1, v___x_2551_);
lean_closure_set(v___x_2562_, 2, v___x_2561_);
v___x_2563_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2550_, v___x_2562_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2563_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_implicitBinder_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2543_ = stack[0].m_num;
lean_object* v_a_2544_ = stack[1].m_obj;
lean_object* v_a_2545_ = stack[2].m_obj;
lean_object* v_a_2546_ = stack[3].m_obj;
lean_object* v_a_2547_ = stack[4].m_obj;
lean_object* v_res_2564_;
v_res_2564_ = l_Lean_Parser_Term_implicitBinder_parenthesizer(v_requireType_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
stack->m_obj
 = v_res_2564_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed(lean_object* v_requireType_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
uint8_t v_requireType_boxed_2571_; lean_object* v_res_2572_; 
v_requireType_boxed_2571_ = lean_unbox(v_requireType_2565_);
v_res_2572_ = l_Lean_Parser_Term_implicitBinder_parenthesizer(v_requireType_boxed_2571_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2572_;
}
}
lean_object* l_Lean_Parser_Term_optIdent_parenthesizer(lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___f_2581_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_parenthesizer___closed__0));
v___x_2582_ = l_Lean_Parser_optional_parenthesizer(v___f_2581_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
return v___x_2582_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optIdent_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2576_ = stack[0].m_obj;
lean_object* v_a_2577_ = stack[1].m_obj;
lean_object* v_a_2578_ = stack[2].m_obj;
lean_object* v_a_2579_ = stack[3].m_obj;
lean_object* v_res_2583_;
v_res_2583_ = l_Lean_Parser_Term_optIdent_parenthesizer(v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
stack->m_obj
 = v_res_2583_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer___boxed(lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Parser_Term_optIdent_parenthesizer(v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
return v_res_2589_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__1));
v___x_2600_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_parenthesizer___boxed), 5, 0);
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2601_, 0, v___x_2600_);
lean_closure_set(v___x_2601_, 1, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2);
v___x_2603_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__4));
v___x_2607_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3);
v___x_2608_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2608_, 0, v___x_2607_);
lean_closure_set(v___x_2608_, 1, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__5, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5);
v___x_2610_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__1));
v___x_2611_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2611_, 0, v___x_2610_);
lean_closure_set(v___x_2611_, 1, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__6, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__6_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6);
v___x_2613_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2614_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__7, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7);
v___x_2615_ = lean_unsigned_to_nat(1024u);
v___x_2616_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2617_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2617_, 0, v___x_2616_);
lean_closure_set(v___x_2617_, 1, v___x_2615_);
lean_closure_set(v___x_2617_, 2, v___x_2614_);
return v___x_2617_;
}
}
lean_object* l_Lean_Parser_Term_instBinder_parenthesizer(lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__0));
v___x_2624_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__8, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8);
v___x_2625_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2623_, v___x_2624_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
return v___x_2625_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_instBinder_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2618_ = stack[0].m_obj;
lean_object* v_a_2619_ = stack[1].m_obj;
lean_object* v_a_2620_ = stack[2].m_obj;
lean_object* v_a_2621_ = stack[3].m_obj;
lean_object* v_res_2626_;
v_res_2626_ = l_Lean_Parser_Term_instBinder_parenthesizer(v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
stack->m_obj
 = v_res_2626_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___boxed(lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Parser_Term_instBinder_parenthesizer(v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
return v_res_2632_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37(){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2640_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2641_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2642_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0));
v___x_2643_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2644_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2640_, v___x_2641_, v___x_2642_, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2645_;
v_res_2645_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
stack->m_obj
 = v_res_2645_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___boxed(lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
return v_res_2647_;
}
}
lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer(uint8_t v_requireType_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2660_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0));
v___x_2661_ = lean_box(v_requireType_2654_);
v___x_2662_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2662_, 0, v___x_2661_);
v___x_2663_ = lean_box(v_requireType_2654_);
v___x_2664_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2664_, 0, v___x_2663_);
v___x_2665_ = lean_box(v_requireType_2654_);
v___x_2666_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2666_, 0, v___x_2665_);
v___x_2667_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2668_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2668_, 0, v___x_2666_);
lean_closure_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2669_, 0, v___x_2664_);
lean_closure_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2670_, 0, v___x_2662_);
lean_closure_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2660_, v___x_2670_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
return v___x_2671_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_bracketedBinder_parenthesizer_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2654_ = stack[0].m_num;
lean_object* v_a_2655_ = stack[1].m_obj;
lean_object* v_a_2656_ = stack[2].m_obj;
lean_object* v_a_2657_ = stack[3].m_obj;
lean_object* v_a_2658_ = stack[4].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l_Lean_Parser_Term_bracketedBinder_parenthesizer(v_requireType_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object* v_requireType_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
uint8_t v_requireType_boxed_2679_; lean_object* v_res_2680_; 
v_requireType_boxed_2679_ = lean_unbox(v_requireType_2673_);
v_res_2680_ = l_Lean_Parser_Term_bracketedBinder_parenthesizer(v_requireType_boxed_2679_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2680_;
}
}
static lean_object* _init_l_Lean_Parser_Term_bracketedBinder___closed__0(void){
_start:
{
uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = 1;
v___x_2682_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2683_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__0));
v___x_2684_ = l_Lean_Parser_mkAntiquot(v___x_2683_, v___x_2682_, v___x_2681_, v___x_2681_);
return v___x_2684_;
}
}
lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t v_requireType_2685_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2686_ = lean_obj_once(&l_Lean_Parser_Term_bracketedBinder___closed__0, &l_Lean_Parser_Term_bracketedBinder___closed__0_once, _init_l_Lean_Parser_Term_bracketedBinder___closed__0);
v___x_2687_ = l_Lean_Parser_Term_explicitBinder(v_requireType_2685_);
v___x_2688_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_2685_);
v___x_2689_ = l_Lean_Parser_Term_implicitBinder(v_requireType_2685_);
v___x_2690_ = l_Lean_Parser_Term_instBinder;
v___x_2691_ = l_Lean_Parser_orelse(v___x_2689_, v___x_2690_);
v___x_2692_ = l_Lean_Parser_orelse(v___x_2688_, v___x_2691_);
v___x_2693_ = l_Lean_Parser_orelse(v___x_2687_, v___x_2692_);
v___x_2694_ = l_Lean_Parser_withAntiquot(v___x_2686_, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_bracketedBinder_0interp(lean_interpreter_value* stack)
{
uint8_t v_requireType_2685_ = stack[0].m_num;
lean_object* v_res_2695_;
v_res_2695_ = l_Lean_Parser_Term_bracketedBinder(v_requireType_2685_);
stack->m_obj
 = v_res_2695_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___boxed(lean_object* v_requireType_2696_){
_start:
{
uint8_t v_requireType_boxed_2697_; lean_object* v_res_2698_; 
v_requireType_boxed_2697_ = lean_unbox(v_requireType_2696_);
v_res_2698_ = l_Lean_Parser_Term_bracketedBinder(v_requireType_boxed_2697_);
return v_res_2698_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1(){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2702_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0));
v___x_2703_ = l_Lean_addBuiltinDocString(v___x_2701_, v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2704_;
v_res_2704_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
stack->m_obj
 = v_res_2704_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___boxed(lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
return v_res_2706_;
}
}
lean_object* l_Lean_Parser_Term_typeSpec_formatter(lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2729_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__2));
v___x_2730_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__3));
v___x_2731_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2729_, v___x_2730_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
return v___x_2731_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_typeSpec_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2724_ = stack[0].m_obj;
lean_object* v_a_2725_ = stack[1].m_obj;
lean_object* v_a_2726_ = stack[2].m_obj;
lean_object* v_a_2727_ = stack[3].m_obj;
lean_object* v_res_2732_;
v_res_2732_ = l_Lean_Parser_Term_typeSpec_formatter(v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
stack->m_obj
 = v_res_2732_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter___boxed(lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Parser_Term_typeSpec_formatter(v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2738_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3(){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2746_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2747_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2748_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0));
v___x_2749_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2750_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2746_, v___x_2747_, v___x_2748_, v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2751_;
v_res_2751_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
stack->m_obj
 = v_res_2751_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___boxed(lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
return v_res_2753_;
}
}
lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer(lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0));
v___x_2771_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1));
v___x_2772_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2770_, v___x_2771_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
return v___x_2772_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_typeSpec_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2765_ = stack[0].m_obj;
lean_object* v_a_2766_ = stack[1].m_obj;
lean_object* v_a_2767_ = stack[2].m_obj;
lean_object* v_a_2768_ = stack[3].m_obj;
lean_object* v_res_2773_;
v_res_2773_ = l_Lean_Parser_Term_typeSpec_parenthesizer(v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
stack->m_obj
 = v_res_2773_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___boxed(lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Parser_Term_typeSpec_parenthesizer(v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2779_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7(){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2787_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2788_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2789_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0));
v___x_2790_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2791_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2787_, v___x_2788_, v___x_2789_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2792_;
v_res_2792_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
stack->m_obj
 = v_res_2792_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___boxed(lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
return v_res_2794_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__0(void){
_start:
{
uint8_t v___x_2795_; uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2795_ = 0;
v___x_2796_ = 1;
v___x_2797_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2798_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__0));
v___x_2799_ = l_Lean_Parser_mkAntiquot(v___x_2798_, v___x_2797_, v___x_2796_, v___x_2795_);
return v___x_2799_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__1(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2800_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_2801_ = lean_unsigned_to_nat(1024u);
v___x_2802_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2803_ = l_Lean_Parser_leadingNode(v___x_2802_, v___x_2801_, v___x_2800_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__2(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__1, &l_Lean_Parser_Term_typeSpec___closed__1_once, _init_l_Lean_Parser_Term_typeSpec___closed__1);
v___x_2805_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__0, &l_Lean_Parser_Term_typeSpec___closed__0_once, _init_l_Lean_Parser_Term_typeSpec___closed__0);
v___x_2806_ = l_Lean_Parser_withAntiquot(v___x_2805_, v___x_2804_);
return v___x_2806_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__3(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__2, &l_Lean_Parser_Term_typeSpec___closed__2_once, _init_l_Lean_Parser_Term_typeSpec___closed__2);
v___x_2808_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2809_ = l_Lean_Parser_withCache(v___x_2808_, v___x_2807_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec(void){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__3, &l_Lean_Parser_Term_typeSpec___closed__3_once, _init_l_Lean_Parser_Term_typeSpec___closed__3);
return v___x_2810_;
}
}
lean_object* l_Lean_Parser_Term_optType_formatter(lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2817_ = l_Lean_Parser_optional_formatter(v___x_2816_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
return v___x_2817_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optType_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2811_ = stack[0].m_obj;
lean_object* v_a_2812_ = stack[1].m_obj;
lean_object* v_a_2813_ = stack[2].m_obj;
lean_object* v_a_2814_ = stack[3].m_obj;
lean_object* v_res_2818_;
v_res_2818_ = l_Lean_Parser_Term_optType_formatter(v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
stack->m_obj
 = v_res_2818_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter___boxed(lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Parser_Term_optType_formatter(v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
return v_res_2824_;
}
}
lean_object* l_Lean_Parser_Term_optType_parenthesizer(lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2831_ = l_Lean_Parser_optional_parenthesizer(v___x_2830_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
return v___x_2831_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optType_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2825_ = stack[0].m_obj;
lean_object* v_a_2826_ = stack[1].m_obj;
lean_object* v_a_2827_ = stack[2].m_obj;
lean_object* v_a_2828_ = stack[3].m_obj;
lean_object* v_res_2832_;
v_res_2832_ = l_Lean_Parser_Term_optType_parenthesizer(v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
stack->m_obj
 = v_res_2832_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer___boxed(lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Parser_Term_optType_parenthesizer(v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
return v_res_2838_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType___closed__0(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = l_Lean_Parser_Term_typeSpec;
v___x_2840_ = l_Lean_Parser_optional(v___x_2839_);
return v___x_2840_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType(void){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_obj_once(&l_Lean_Parser_Term_optType___closed__0, &l_Lean_Parser_Term_optType___closed__0_once, _init_l_Lean_Parser_Term_optType___closed__0);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_unsigned_to_nat(2382944618u);
v___x_2873_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2874_ = l_Lean_Name_num___override(v___x_2873_, v___x_2872_);
return v___x_2874_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2876_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2877_ = l_Lean_Name_str___override(v___x_2876_, v___x_2875_);
return v___x_2877_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2879_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2880_ = l_Lean_Name_str___override(v___x_2879_, v___x_2878_);
return v___x_2880_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_unsigned_to_nat(2u);
v___x_2882_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2883_ = l_Lean_Name_num___override(v___x_2882_, v___x_2881_);
return v___x_2883_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2885_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2886_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2887_ = 0;
v___x_2888_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2889_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_2885_, v___x_2886_, v___x_2887_, v___x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2890_;
v_res_2890_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2890_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2____boxed(lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser(lean_object* v_rbp_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_2897_ = l_Lean_Parser_categoryParser(v___x_2896_, v_rbp_2895_);
return v___x_2897_;
}
}
lean_object* l_Lean_Parser_Term_optEllipsis_formatter(lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__2));
v___x_2926_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__6));
v___x_2927_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2925_, v___x_2926_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
return v___x_2927_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optEllipsis_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2920_ = stack[0].m_obj;
lean_object* v_a_2921_ = stack[1].m_obj;
lean_object* v_a_2922_ = stack[2].m_obj;
lean_object* v_a_2923_ = stack[3].m_obj;
lean_object* v_res_2928_;
v_res_2928_ = l_Lean_Parser_Term_optEllipsis_formatter(v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
stack->m_obj
 = v_res_2928_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter___boxed(lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Parser_Term_optEllipsis_formatter(v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
return v_res_2934_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3(){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2942_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2943_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2944_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0));
v___x_2945_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_formatter___boxed), 5, 0);
v___x_2946_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2942_, v___x_2943_, v___x_2944_, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2947_;
v_res_2947_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
stack->m_obj
 = v_res_2947_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___boxed(lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
return v_res_2949_;
}
}
lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer(lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0));
v___x_2971_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3));
v___x_2972_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2970_, v___x_2971_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_2972_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optEllipsis_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2965_ = stack[0].m_obj;
lean_object* v_a_2966_ = stack[1].m_obj;
lean_object* v_a_2967_ = stack[2].m_obj;
lean_object* v_a_2968_ = stack[3].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l_Lean_Parser_Term_optEllipsis_parenthesizer(v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed(lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_Parser_Term_optEllipsis_parenthesizer(v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
return v_res_2979_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7(){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2987_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2988_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2989_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0));
v___x_2990_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed), 5, 0);
v___x_2991_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2987_, v___x_2988_, v___x_2989_, v___x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2992_;
v_res_2992_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
stack->m_obj
 = v_res_2992_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___boxed(lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
return v_res_2994_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__0(void){
_start:
{
uint8_t v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2995_ = 0;
v___x_2996_ = 1;
v___x_2997_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2998_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__0));
v___x_2999_ = l_Lean_Parser_mkAntiquot(v___x_2998_, v___x_2997_, v___x_2996_, v___x_2995_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__1(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__3));
v___x_3001_ = l_Lean_Parser_symbol(v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__2(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__1, &l_Lean_Parser_Term_optEllipsis___closed__1_once, _init_l_Lean_Parser_Term_optEllipsis___closed__1);
v___x_3003_ = l_Lean_Parser_optional(v___x_3002_);
return v___x_3003_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__3(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3004_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__2, &l_Lean_Parser_Term_optEllipsis___closed__2_once, _init_l_Lean_Parser_Term_optEllipsis___closed__2);
v___x_3005_ = lean_unsigned_to_nat(1024u);
v___x_3006_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_3007_ = l_Lean_Parser_leadingNode(v___x_3006_, v___x_3005_, v___x_3004_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__4(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__3, &l_Lean_Parser_Term_optEllipsis___closed__3_once, _init_l_Lean_Parser_Term_optEllipsis___closed__3);
v___x_3009_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__0, &l_Lean_Parser_Term_optEllipsis___closed__0_once, _init_l_Lean_Parser_Term_optEllipsis___closed__0);
v___x_3010_ = l_Lean_Parser_withAntiquot(v___x_3009_, v___x_3008_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__5(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__4, &l_Lean_Parser_Term_optEllipsis___closed__4_once, _init_l_Lean_Parser_Term_optEllipsis___closed__4);
v___x_3012_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_3013_ = l_Lean_Parser_withCache(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis(void){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__5, &l_Lean_Parser_Term_optEllipsis___closed__5_once, _init_l_Lean_Parser_Term_optEllipsis___closed__5);
return v___x_3014_;
}
}
lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter(lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2));
v___x_3046_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6));
v___x_3047_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3045_, v___x_3046_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
return v___x_3047_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstArrayRef_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3040_ = stack[0].m_obj;
lean_object* v_a_3041_ = stack[1].m_obj;
lean_object* v_a_3042_ = stack[2].m_obj;
lean_object* v_a_3043_ = stack[3].m_obj;
lean_object* v_res_3048_;
v_res_3048_ = l_Lean_Parser_Term_structInstArrayRef_formatter(v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
stack->m_obj
 = v_res_3048_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___boxed(lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Parser_Term_structInstArrayRef_formatter(v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3054_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3(){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3062_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3063_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3064_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0));
v___x_3065_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3066_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3062_, v___x_3063_, v___x_3064_, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3067_;
v_res_3067_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
stack->m_obj
 = v_res_3067_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___boxed(lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
return v_res_3069_;
}
}
lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer(lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0));
v___x_3095_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4));
v___x_3096_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3094_, v___x_3095_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
return v___x_3096_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstArrayRef_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3089_ = stack[0].m_obj;
lean_object* v_a_3090_ = stack[1].m_obj;
lean_object* v_a_3091_ = stack[2].m_obj;
lean_object* v_a_3092_ = stack[3].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l_Lean_Parser_Term_structInstArrayRef_parenthesizer(v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed(lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Parser_Term_structInstArrayRef_parenthesizer(v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
return v_res_3103_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7(){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3111_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3112_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3113_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0));
v___x_3114_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3115_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3111_, v___x_3112_, v___x_3113_, v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3116_;
v_res_3116_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
stack->m_obj
 = v_res_3116_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___boxed(lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
return v_res_3118_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__0(void){
_start:
{
uint8_t v___x_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3119_ = 0;
v___x_3120_ = 1;
v___x_3121_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3122_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0));
v___x_3123_ = l_Lean_Parser_mkAntiquot(v___x_3122_, v___x_3121_, v___x_3120_, v___x_3119_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__1(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_3125_ = l_Lean_Parser_withoutPosition(v___x_3124_);
return v___x_3125_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__2(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_3127_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__1, &l_Lean_Parser_Term_structInstArrayRef___closed__1_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__1);
v___x_3128_ = l_Lean_Parser_andthen(v___x_3127_, v___x_3126_);
return v___x_3128_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__3(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__2, &l_Lean_Parser_Term_structInstArrayRef___closed__2_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__2);
v___x_3130_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_3131_ = l_Lean_Parser_andthen(v___x_3130_, v___x_3129_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__4(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__3, &l_Lean_Parser_Term_structInstArrayRef___closed__3_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__3);
v___x_3133_ = lean_unsigned_to_nat(1024u);
v___x_3134_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3135_ = l_Lean_Parser_leadingNode(v___x_3134_, v___x_3133_, v___x_3132_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__5(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__4, &l_Lean_Parser_Term_structInstArrayRef___closed__4_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__4);
v___x_3137_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__0, &l_Lean_Parser_Term_structInstArrayRef___closed__0_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__0);
v___x_3138_ = l_Lean_Parser_withAntiquot(v___x_3137_, v___x_3136_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__6(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__5, &l_Lean_Parser_Term_structInstArrayRef___closed__5_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__5);
v___x_3140_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3141_ = l_Lean_Parser_withCache(v___x_3140_, v___x_3139_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef(void){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__6, &l_Lean_Parser_Term_structInstArrayRef___closed__6_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__6);
return v___x_3142_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3157_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3158_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3158_, 0, v___x_3157_);
lean_closure_set(v___x_3158_, 1, v___x_3156_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__3, &l_Lean_Parser_Term_structInstLVal_formatter___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3);
v___x_3160_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3161_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3161_, 0, v___x_3160_);
lean_closure_set(v___x_3161_, 1, v___x_3159_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3166_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3167_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3167_, 0, v___x_3166_);
lean_closure_set(v___x_3167_, 1, v___x_3165_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__7, &l_Lean_Parser_Term_structInstLVal_formatter___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7);
v___x_3169_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__6));
v___x_3170_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3170_, 0, v___x_3169_);
lean_closure_set(v___x_3170_, 1, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__8, &l_Lean_Parser_Term_structInstLVal_formatter___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8);
v___x_3172_ = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter___boxed), 6, 1);
lean_closure_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3174_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__9, &l_Lean_Parser_Term_structInstLVal_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9);
v___x_3175_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3175_, 0, v___x_3174_);
lean_closure_set(v___x_3175_, 1, v___x_3173_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__10, &l_Lean_Parser_Term_structInstLVal_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10);
v___x_3177_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__11, &l_Lean_Parser_Term_structInstLVal_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11);
v___x_3179_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__4, &l_Lean_Parser_Term_structInstLVal_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4);
v___x_3180_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3180_, 0, v___x_3179_);
lean_closure_set(v___x_3180_, 1, v___x_3178_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3181_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__12, &l_Lean_Parser_Term_structInstLVal_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12);
v___x_3182_ = lean_unsigned_to_nat(1024u);
v___x_3183_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3184_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3184_, 0, v___x_3183_);
lean_closure_set(v___x_3184_, 1, v___x_3182_);
lean_closure_set(v___x_3184_, 2, v___x_3181_);
return v___x_3184_;
}
}
lean_object* l_Lean_Parser_Term_structInstLVal_formatter(lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__2));
v___x_3191_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__13, &l_Lean_Parser_Term_structInstLVal_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13);
v___x_3192_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3190_, v___x_3191_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
return v___x_3192_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstLVal_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3185_ = stack[0].m_obj;
lean_object* v_a_3186_ = stack[1].m_obj;
lean_object* v_a_3187_ = stack[2].m_obj;
lean_object* v_a_3188_ = stack[3].m_obj;
lean_object* v_res_3193_;
v_res_3193_ = l_Lean_Parser_Term_structInstLVal_formatter(v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
stack->m_obj
 = v_res_3193_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter___boxed(lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Parser_Term_structInstLVal_formatter(v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
return v_res_3199_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3(){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3207_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3208_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3209_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0));
v___x_3210_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3211_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3207_, v___x_3208_, v___x_3209_, v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3212_;
v_res_3212_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
stack->m_obj
 = v_res_3212_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___boxed(lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
return v_res_3214_;
}
}
lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_3216_);
return v___x_3220_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3215_ = stack[0].m_obj;
lean_object* v___y_3216_ = stack[1].m_obj;
lean_object* v___y_3217_ = stack[2].m_obj;
lean_object* v___y_3218_ = stack[3].m_obj;
lean_object* v_res_3221_;
v_res_3221_ = l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
stack->m_obj
 = v_res_3221_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0___boxed(lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3227_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___f_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___f_3237_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0));
v___x_3238_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3238_, 0, v___f_3237_);
lean_closure_set(v___x_3238_, 1, v___x_3236_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2);
v___x_3240_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_3241_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3241_, 0, v___x_3240_);
lean_closure_set(v___x_3241_, 1, v___x_3239_);
return v___x_3241_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3253_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7));
v___x_3254_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3254_, 0, v___x_3253_);
lean_closure_set(v___x_3254_, 1, v___x_3252_);
return v___x_3254_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8);
v___x_3256_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9);
v___x_3258_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3);
v___x_3259_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3259_, 0, v___x_3258_);
lean_closure_set(v___x_3259_, 1, v___x_3257_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3260_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10);
v___x_3261_ = lean_unsigned_to_nat(1024u);
v___x_3262_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3263_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3263_, 0, v___x_3262_);
lean_closure_set(v___x_3263_, 1, v___x_3261_);
lean_closure_set(v___x_3263_, 2, v___x_3260_);
return v___x_3263_;
}
}
lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer(lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1));
v___x_3270_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11);
v___x_3271_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3269_, v___x_3270_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
return v___x_3271_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstLVal_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3264_ = stack[0].m_obj;
lean_object* v_a_3265_ = stack[1].m_obj;
lean_object* v_a_3266_ = stack[2].m_obj;
lean_object* v_a_3267_ = stack[3].m_obj;
lean_object* v_res_3272_;
v_res_3272_ = l_Lean_Parser_Term_structInstLVal_parenthesizer(v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
stack->m_obj
 = v_res_3272_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed(lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Parser_Term_structInstLVal_parenthesizer(v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
return v_res_3278_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7(){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3286_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3287_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3288_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0));
v___x_3289_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3290_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3286_, v___x_3287_, v___x_3288_, v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3291_;
v_res_3291_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
stack->m_obj
 = v_res_3291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___boxed(lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
return v_res_3293_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__0(void){
_start:
{
uint8_t v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3294_ = 0;
v___x_3295_ = 1;
v___x_3296_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3297_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__0));
v___x_3298_ = l_Lean_Parser_mkAntiquot(v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__1(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3300_ = l_Lean_Parser_fieldIdx;
v___x_3301_ = l_Lean_Parser_orelse(v___x_3300_, v___x_3299_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__2(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__1, &l_Lean_Parser_Term_structInstLVal___closed__1_once, _init_l_Lean_Parser_Term_structInstLVal___closed__1);
v___x_3303_ = l_Lean_Parser_ident;
v___x_3304_ = l_Lean_Parser_orelse(v___x_3303_, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__3(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__5));
v___x_3306_ = l_Lean_Parser_symbol(v___x_3305_);
return v___x_3306_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__4(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = l_Lean_Parser_fieldIdx;
v___x_3308_ = l_Lean_Parser_ident;
v___x_3309_ = l_Lean_Parser_orelse(v___x_3308_, v___x_3307_);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__5(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__4, &l_Lean_Parser_Term_structInstLVal___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal___closed__4);
v___x_3311_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__3, &l_Lean_Parser_Term_structInstLVal___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal___closed__3);
v___x_3312_ = l_Lean_Parser_andthen(v___x_3311_, v___x_3310_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__6(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__5, &l_Lean_Parser_Term_structInstLVal___closed__5_once, _init_l_Lean_Parser_Term_structInstLVal___closed__5);
v___x_3314_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_3315_ = l_Lean_Parser_node(v___x_3314_, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__7(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3317_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__6, &l_Lean_Parser_Term_structInstLVal___closed__6_once, _init_l_Lean_Parser_Term_structInstLVal___closed__6);
v___x_3318_ = l_Lean_Parser_orelse(v___x_3317_, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__8(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__7, &l_Lean_Parser_Term_structInstLVal___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal___closed__7);
v___x_3320_ = l_Lean_Parser_many(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__9(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__8, &l_Lean_Parser_Term_structInstLVal___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal___closed__8);
v___x_3322_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__2, &l_Lean_Parser_Term_structInstLVal___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal___closed__2);
v___x_3323_ = l_Lean_Parser_andthen(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__10(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3324_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__9, &l_Lean_Parser_Term_structInstLVal___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal___closed__9);
v___x_3325_ = lean_unsigned_to_nat(1024u);
v___x_3326_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3327_ = l_Lean_Parser_leadingNode(v___x_3326_, v___x_3325_, v___x_3324_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__11(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__10, &l_Lean_Parser_Term_structInstLVal___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal___closed__10);
v___x_3329_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__0, &l_Lean_Parser_Term_structInstLVal___closed__0_once, _init_l_Lean_Parser_Term_structInstLVal___closed__0);
v___x_3330_ = l_Lean_Parser_withAntiquot(v___x_3329_, v___x_3328_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__12(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__11, &l_Lean_Parser_Term_structInstLVal___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal___closed__11);
v___x_3332_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3333_ = l_Lean_Parser_withCache(v___x_3332_, v___x_3331_);
return v___x_3333_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal(void){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__12, &l_Lean_Parser_Term_structInstLVal___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal___closed__12);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3));
v___x_3351_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_3352_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3352_, 0, v___x_3351_);
lean_closure_set(v___x_3352_, 1, v___x_3350_);
return v___x_3352_;
}
}
lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter(lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3358_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2));
v___x_3359_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4, &l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4);
v___x_3360_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3358_, v___x_3359_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
return v___x_3360_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFieldBinder_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3353_ = stack[0].m_obj;
lean_object* v_a_3354_ = stack[1].m_obj;
lean_object* v_a_3355_ = stack[2].m_obj;
lean_object* v_a_3356_ = stack[3].m_obj;
lean_object* v_res_3361_;
v_res_3361_ = l_Lean_Parser_Term_structInstFieldBinder_formatter(v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
stack->m_obj
 = v_res_3361_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed(lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Parser_Term_structInstFieldBinder_formatter(v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3367_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1));
v___x_3378_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_3379_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3379_, 0, v___x_3378_);
lean_closure_set(v___x_3379_, 1, v___x_3377_);
return v___x_3379_;
}
}
lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0));
v___x_3386_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2);
v___x_3387_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3385_, v___x_3386_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v___x_3387_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFieldBinder_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3380_ = stack[0].m_obj;
lean_object* v_a_3381_ = stack[1].m_obj;
lean_object* v_a_3382_ = stack[2].m_obj;
lean_object* v_a_3383_ = stack[3].m_obj;
lean_object* v_res_3388_;
v_res_3388_ = l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
stack->m_obj
 = v_res_3388_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed(lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
return v_res_3394_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0(void){
_start:
{
uint8_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = 1;
v___x_3396_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1));
v___x_3397_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0));
v___x_3398_ = l_Lean_Parser_mkAntiquot(v___x_3397_, v___x_3396_, v___x_3395_, v___x_3395_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1(void){
_start:
{
uint8_t v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = 0;
v___x_3400_ = l_Lean_Parser_Term_bracketedBinder(v___x_3399_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__1, &l_Lean_Parser_Term_structInstFieldBinder___closed__1_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1);
v___x_3402_ = l_Lean_Parser_Term_binderIdent;
v___x_3403_ = l_Lean_Parser_orelse(v___x_3402_, v___x_3401_);
return v___x_3403_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__2, &l_Lean_Parser_Term_structInstFieldBinder___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2);
v___x_3405_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__0, &l_Lean_Parser_Term_structInstFieldBinder___closed__0_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0);
v___x_3406_ = l_Lean_Parser_withAntiquot(v___x_3405_, v___x_3404_);
return v___x_3406_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder(void){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__3, &l_Lean_Parser_Term_structInstFieldBinder___closed__3_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0));
v___x_3411_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_3412_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3412_, 0, v___x_3411_);
lean_closure_set(v___x_3412_, 1, v___x_3410_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1);
v___x_3414_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter(lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2);
v___x_3421_ = l_Lean_Parser_optional_formatter(v___x_3420_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
return v___x_3421_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optTypeForStructInst_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3415_ = stack[0].m_obj;
lean_object* v_a_3416_ = stack[1].m_obj;
lean_object* v_a_3417_ = stack[2].m_obj;
lean_object* v_a_3418_ = stack[3].m_obj;
lean_object* v_res_3422_;
v_res_3422_ = l_Lean_Parser_Term_optTypeForStructInst_formatter(v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
stack->m_obj
 = v_res_3422_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed(lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Parser_Term_optTypeForStructInst_formatter(v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
return v_res_3428_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; 
v___x_3431_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0));
v___x_3432_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3433_, 0, v___x_3432_);
lean_closure_set(v___f_3433_, 1, v___x_3431_);
return v___f_3433_;
}
}
lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v___f_3439_; lean_object* v___x_3440_; 
v___f_3439_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1);
v___x_3440_ = l_Lean_Parser_optional_parenthesizer(v___f_3439_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3440_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_optTypeForStructInst_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3434_ = stack[0].m_obj;
lean_object* v_a_3435_ = stack[1].m_obj;
lean_object* v_a_3436_ = stack[2].m_obj;
lean_object* v_a_3437_ = stack[3].m_obj;
lean_object* v_res_3441_;
v_res_3441_ = l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
stack->m_obj
 = v_res_3441_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed(lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
return v_res_3447_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_3449_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_3450_ = l_Lean_Parser_notFollowedBy(v___x_3449_, v___x_3448_);
return v___x_3450_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__0, &l_Lean_Parser_Term_optTypeForStructInst___closed__0_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0);
v___x_3452_ = l_Lean_Parser_Term_typeSpec;
v___x_3453_ = l_Lean_Parser_andthen(v___x_3452_, v___x_3451_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__1, &l_Lean_Parser_Term_optTypeForStructInst___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1);
v___x_3455_ = l_Lean_Parser_atomic(v___x_3454_);
return v___x_3455_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3(void){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__2, &l_Lean_Parser_Term_optTypeForStructInst___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2);
v___x_3457_ = l_Lean_Parser_optional(v___x_3456_);
return v___x_3457_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst(void){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__3, &l_Lean_Parser_Term_optTypeForStructInst___closed__3_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3);
return v___x_3458_;
}
}
lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3465_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_3464_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
return v___x_3465_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3459_ = stack[0].m_obj;
lean_object* v_a_3460_ = stack[1].m_obj;
lean_object* v_a_3461_ = stack[2].m_obj;
lean_object* v_a_3462_ = stack[3].m_obj;
lean_object* v_res_3466_;
v_res_3466_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
stack->m_obj
 = v_res_3466_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg___boxed(lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
return v_res_3472_;
}
}
lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter(lean_object* v_rbp_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
return v___x_3479_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFieldDeclParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_3473_ = stack[0].m_obj;
lean_object* v_a_3474_ = stack[1].m_obj;
lean_object* v_a_3475_ = stack[2].m_obj;
lean_object* v_a_3476_ = stack[3].m_obj;
lean_object* v_a_3477_ = stack[4].m_obj;
lean_object* v_res_3480_;
v_res_3480_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter(v_rbp_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
stack->m_obj
 = v_res_3480_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___boxed(lean_object* v_rbp_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter(v_rbp_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_rbp_3481_);
return v_res_3487_;
}
}
lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0(lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3489_);
return v___x_3493_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstField_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3488_ = stack[0].m_obj;
lean_object* v___y_3489_ = stack[1].m_obj;
lean_object* v___y_3490_ = stack[2].m_obj;
lean_object* v___y_3491_ = stack[3].m_obj;
lean_object* v_res_3494_;
v_res_3494_ = l_Lean_Parser_Term_structInstField_formatter___lam__0(v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
stack->m_obj
 = v_res_3494_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0___boxed(lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Parser_Term_structInstField_formatter___lam__0(v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
return v_res_3500_;
}
}
lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1(lean_object* v___x_3501_, lean_object* v___x_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3501_, v___x_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
return v___x_3508_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstField_formatter___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3501_ = stack[0].m_obj;
lean_object* v___x_3502_ = stack[1].m_obj;
lean_object* v___y_3503_ = stack[2].m_obj;
lean_object* v___y_3504_ = stack[3].m_obj;
lean_object* v___y_3505_ = stack[4].m_obj;
lean_object* v___y_3506_ = stack[5].m_obj;
lean_object* v_res_3509_;
v_res_3509_ = l_Lean_Parser_Term_structInstField_formatter___lam__1(v___x_3501_, v___x_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
stack->m_obj
 = v_res_3509_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed(lean_object* v___x_3510_, lean_object* v___x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Parser_Term_structInstField_formatter___lam__1(v___x_3510_, v___x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
return v_res_3517_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__4(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___f_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed), 5, 0);
v___f_3533_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__0));
v___x_3534_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3534_, 0, v___f_3533_);
lean_closure_set(v___x_3534_, 1, v___x_3532_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__5(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__4, &l_Lean_Parser_Term_structInstField_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__4);
v___x_3536_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_3537_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3537_, 0, v___x_3536_);
lean_closure_set(v___x_3537_, 1, v___x_3535_);
return v___x_3537_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__6(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__5, &l_Lean_Parser_Term_structInstField_formatter___closed__5_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__5);
v___x_3539_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3539_, 0, v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__9(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__8));
v___x_3545_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed), 5, 0);
v___x_3546_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3546_, 0, v___x_3545_);
lean_closure_set(v___x_3546_, 1, v___x_3544_);
return v___x_3546_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__10(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__9, &l_Lean_Parser_Term_structInstField_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__9);
v___x_3548_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__6, &l_Lean_Parser_Term_structInstField_formatter___closed__6_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__6);
v___x_3549_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3549_, 0, v___x_3548_);
lean_closure_set(v___x_3549_, 1, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__11(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__10, &l_Lean_Parser_Term_structInstField_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__10);
v___x_3551_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__12(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__11, &l_Lean_Parser_Term_structInstField_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__11);
v___x_3553_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3554_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3554_, 0, v___x_3553_);
lean_closure_set(v___x_3554_, 1, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__13(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3555_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__12, &l_Lean_Parser_Term_structInstField_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__12);
v___x_3556_ = lean_unsigned_to_nat(1024u);
v___x_3557_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3558_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3558_, 0, v___x_3557_);
lean_closure_set(v___x_3558_, 1, v___x_3556_);
lean_closure_set(v___x_3558_, 2, v___x_3555_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__14(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___f_3561_; 
v___x_3559_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__13, &l_Lean_Parser_Term_structInstField_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__13);
v___x_3560_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__3));
v___f_3561_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed), 7, 2);
lean_closure_set(v___f_3561_, 0, v___x_3560_);
lean_closure_set(v___f_3561_, 1, v___x_3559_);
return v___f_3561_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__15(void){
_start:
{
lean_object* v___f_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___f_3562_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__14, &l_Lean_Parser_Term_structInstField_formatter___closed__14_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__14);
v___x_3563_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3564_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_formatter___boxed), 7, 2);
lean_closure_set(v___x_3564_, 0, v___x_3563_);
lean_closure_set(v___x_3564_, 1, v___f_3562_);
return v___x_3564_;
}
}
lean_object* l_Lean_Parser_Term_structInstField_formatter(lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__15, &l_Lean_Parser_Term_structInstField_formatter___closed__15_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__15);
v___x_3571_ = l_Lean_Parser_ppGroup_formatter(v___x_3570_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
return v___x_3571_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstField_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3565_ = stack[0].m_obj;
lean_object* v_a_3566_ = stack[1].m_obj;
lean_object* v_a_3567_ = stack[2].m_obj;
lean_object* v_a_3568_ = stack[3].m_obj;
lean_object* v_res_3572_;
v_res_3572_ = l_Lean_Parser_Term_structInstField_formatter(v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
stack->m_obj
 = v_res_3572_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Parser_Term_structInstField_formatter(v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
return v_res_3578_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5(){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3586_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3587_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3588_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0));
v___x_3589_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___boxed), 5, 0);
v___x_3590_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3586_, v___x_3587_, v___x_3588_, v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3591_;
v_res_3591_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
stack->m_obj
 = v_res_3591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___boxed(lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
return v_res_3593_;
}
}
lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(lean_object* v_rbp_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3601_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_3600_, v_rbp_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_);
return v___x_3601_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_3594_ = stack[0].m_obj;
lean_object* v_a_3595_ = stack[1].m_obj;
lean_object* v_a_3596_ = stack[2].m_obj;
lean_object* v_a_3597_ = stack[3].m_obj;
lean_object* v_a_3598_ = stack[4].m_obj;
lean_object* v_res_3602_;
v_res_3602_ = l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(v_rbp_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_);
stack->m_obj
 = v_res_3602_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer___boxed(lean_object* v_rbp_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(v_rbp_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
return v_res_3609_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed), 5, 0);
v___x_3619_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__1));
v___x_3620_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3620_, 0, v___x_3619_);
lean_closure_set(v___x_3620_, 1, v___x_3618_);
return v___x_3620_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2);
v___x_3622_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_3623_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3623_, 0, v___x_3622_);
lean_closure_set(v___x_3623_, 1, v___x_3621_);
return v___x_3623_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3);
v___x_3625_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3625_, 0, v___x_3624_);
return v___x_3625_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__6));
v___x_3631_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed), 5, 0);
v___x_3632_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3632_, 0, v___x_3631_);
lean_closure_set(v___x_3632_, 1, v___x_3630_);
return v___x_3632_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__7, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7);
v___x_3634_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__4, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4);
v___x_3635_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3635_, 0, v___x_3634_);
lean_closure_set(v___x_3635_, 1, v___x_3633_);
return v___x_3635_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8);
v___x_3637_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3637_, 0, v___x_3636_);
return v___x_3637_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9);
v___x_3639_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3640_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3640_, 0, v___x_3639_);
lean_closure_set(v___x_3640_, 1, v___x_3638_);
return v___x_3640_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3641_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10);
v___x_3642_ = lean_unsigned_to_nat(1024u);
v___x_3643_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3644_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3644_, 0, v___x_3643_);
lean_closure_set(v___x_3644_, 1, v___x_3642_);
lean_closure_set(v___x_3644_, 2, v___x_3641_);
return v___x_3644_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11);
v___x_3646_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__0));
v___x_3647_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3647_, 0, v___x_3646_);
lean_closure_set(v___x_3647_, 1, v___x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__12, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__12_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12);
v___x_3649_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3650_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3650_, 0, v___x_3649_);
lean_closure_set(v___x_3650_, 1, v___x_3648_);
return v___x_3650_;
}
}
lean_object* l_Lean_Parser_Term_structInstField_parenthesizer(lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__13, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__13_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13);
v___x_3657_ = l_Lean_Parser_ppGroup_parenthesizer(v___x_3656_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
return v___x_3657_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstField_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3651_ = stack[0].m_obj;
lean_object* v_a_3652_ = stack[1].m_obj;
lean_object* v_a_3653_ = stack[2].m_obj;
lean_object* v_a_3654_ = stack[3].m_obj;
lean_object* v_res_3658_;
v_res_3658_ = l_Lean_Parser_Term_structInstField_parenthesizer(v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
stack->m_obj
 = v_res_3658_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Parser_Term_structInstField_parenthesizer(v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
return v_res_3664_;
}
}
lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11(){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3672_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3673_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3674_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0));
v___x_3675_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_parenthesizer___boxed), 5, 0);
v___x_3676_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3672_, v___x_3673_, v___x_3674_, v___x_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3677_;
v_res_3677_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
stack->m_obj
 = v_res_3677_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___boxed(lean_object* v_a_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
return v_res_3679_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__0(void){
_start:
{
uint8_t v___x_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3680_ = 0;
v___x_3681_ = 1;
v___x_3682_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3683_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__1));
v___x_3684_ = l_Lean_Parser_mkAntiquot(v___x_3683_, v___x_3682_, v___x_3681_, v___x_3680_);
return v___x_3684_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__2(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = ((lean_object*)(l_Lean_Parser_Term_structInstField___closed__1));
v___x_3687_ = l_Lean_Parser_checkColGt(v___x_3686_);
return v___x_3687_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__3(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3688_ = l_Lean_Parser_Term_structInstFieldBinder;
v___x_3689_ = l_Lean_Parser_skip;
v___x_3690_ = l_Lean_Parser_andthen(v___x_3689_, v___x_3688_);
return v___x_3690_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__4(void){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3691_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__3, &l_Lean_Parser_Term_structInstField___closed__3_once, _init_l_Lean_Parser_Term_structInstField___closed__3);
v___x_3692_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__2, &l_Lean_Parser_Term_structInstField___closed__2_once, _init_l_Lean_Parser_Term_structInstField___closed__2);
v___x_3693_ = l_Lean_Parser_andthen(v___x_3692_, v___x_3691_);
return v___x_3693_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__5(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__4, &l_Lean_Parser_Term_structInstField___closed__4_once, _init_l_Lean_Parser_Term_structInstField___closed__4);
v___x_3695_ = l_Lean_Parser_many(v___x_3694_);
return v___x_3695_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__6(void){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3696_ = lean_unsigned_to_nat(0u);
v___x_3697_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3698_ = l_Lean_Parser_categoryParser(v___x_3697_, v___x_3696_);
return v___x_3698_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__7(void){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__6, &l_Lean_Parser_Term_structInstField___closed__6_once, _init_l_Lean_Parser_Term_structInstField___closed__6);
v___x_3700_ = l_Lean_Parser_Term_optTypeForStructInst;
v___x_3701_ = l_Lean_Parser_andthen(v___x_3700_, v___x_3699_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__8(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__7, &l_Lean_Parser_Term_structInstField___closed__7_once, _init_l_Lean_Parser_Term_structInstField___closed__7);
v___x_3703_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__5, &l_Lean_Parser_Term_structInstField___closed__5_once, _init_l_Lean_Parser_Term_structInstField___closed__5);
v___x_3704_ = l_Lean_Parser_andthen(v___x_3703_, v___x_3702_);
return v___x_3704_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__9(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__8, &l_Lean_Parser_Term_structInstField___closed__8_once, _init_l_Lean_Parser_Term_structInstField___closed__8);
v___x_3706_ = l_Lean_Parser_optional(v___x_3705_);
return v___x_3706_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__10(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__9, &l_Lean_Parser_Term_structInstField___closed__9_once, _init_l_Lean_Parser_Term_structInstField___closed__9);
v___x_3708_ = l_Lean_Parser_Term_structInstLVal;
v___x_3709_ = l_Lean_Parser_andthen(v___x_3708_, v___x_3707_);
return v___x_3709_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__11(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3710_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__10, &l_Lean_Parser_Term_structInstField___closed__10_once, _init_l_Lean_Parser_Term_structInstField___closed__10);
v___x_3711_ = lean_unsigned_to_nat(1024u);
v___x_3712_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3713_ = l_Lean_Parser_leadingNode(v___x_3712_, v___x_3711_, v___x_3710_);
return v___x_3713_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__12(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__11, &l_Lean_Parser_Term_structInstField___closed__11_once, _init_l_Lean_Parser_Term_structInstField___closed__11);
v___x_3715_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__0, &l_Lean_Parser_Term_structInstField___closed__0_once, _init_l_Lean_Parser_Term_structInstField___closed__0);
v___x_3716_ = l_Lean_Parser_withAntiquot(v___x_3715_, v___x_3714_);
return v___x_3716_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__13(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__12, &l_Lean_Parser_Term_structInstField___closed__12_once, _init_l_Lean_Parser_Term_structInstField___closed__12);
v___x_3718_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3719_ = l_Lean_Parser_withCache(v___x_3718_, v___x_3717_);
return v___x_3719_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField(void){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__13, &l_Lean_Parser_Term_structInstField___closed__13_once, _init_l_Lean_Parser_Term_structInstField___closed__13);
return v___x_3720_;
}
}
lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object* v_p_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3734_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_3733_, v_p_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
return v___x_3734_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFields_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3727_ = stack[0].m_obj;
lean_object* v_a_3728_ = stack[1].m_obj;
lean_object* v_a_3729_ = stack[2].m_obj;
lean_object* v_a_3730_ = stack[3].m_obj;
lean_object* v_a_3731_ = stack[4].m_obj;
lean_object* v_res_3735_;
v_res_3735_ = l_Lean_Parser_Term_structInstFields_formatter(v_p_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
stack->m_obj
 = v_res_3735_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter___boxed(lean_object* v_p_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Parser_Term_structInstFields_formatter(v_p_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
return v_res_3742_;
}
}
lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object* v_p_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3750_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_3749_, v_p_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
return v___x_3750_;
}
}
LEAN_EXPORT void l_Lean_Parser_Term_structInstFields_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3743_ = stack[0].m_obj;
lean_object* v_a_3744_ = stack[1].m_obj;
lean_object* v_a_3745_ = stack[2].m_obj;
lean_object* v_a_3746_ = stack[3].m_obj;
lean_object* v_a_3747_ = stack[4].m_obj;
lean_object* v_res_3751_;
v_res_3751_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v_p_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
stack->m_obj
 = v_res_3751_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer___boxed(lean_object* v_p_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v_p_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_a_3754_);
lean_dec_ref(v_a_3753_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields(lean_object* v_p_3759_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3761_ = l_Lean_Parser_node(v___x_3760_, v_p_3759_);
return v___x_3761_;
}
}
lean_object* runtime_initialize_Lean_Parser_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticSeq1Indented = _init_l_Lean_Parser_Tactic_tacticSeq1Indented();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeq1Indented);
l_Lean_Parser_Tactic_tacticSeqBracketed = _init_l_Lean_Parser_Tactic_tacticSeqBracketed();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeqBracketed);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticSeq = _init_l_Lean_Parser_Tactic_tacticSeq();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeq);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticSeqIndentGt = _init_l_Lean_Parser_Tactic_tacticSeqIndentGt();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeqIndentGt);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_seq1 = _init_l_Lean_Parser_Tactic_seq1();
lean_mark_persistent(l_Lean_Parser_Tactic_seq1);
l_Lean_Parser_Term_hole = _init_l_Lean_Parser_Term_hole();
lean_mark_persistent(l_Lean_Parser_Term_hole);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_syntheticHole = _init_l_Lean_Parser_Term_syntheticHole();
lean_mark_persistent(l_Lean_Parser_Term_syntheticHole);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_omission = _init_l_Lean_Parser_Term_omission();
lean_mark_persistent(l_Lean_Parser_Term_omission);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_binderIdent = _init_l_Lean_Parser_Term_binderIdent();
lean_mark_persistent(l_Lean_Parser_Term_binderIdent);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_binderTactic = _init_l_Lean_Parser_Term_binderTactic();
lean_mark_persistent(l_Lean_Parser_Term_binderTactic);
l_Lean_Parser_Term_binderDefault = _init_l_Lean_Parser_Term_binderDefault();
lean_mark_persistent(l_Lean_Parser_Term_binderDefault);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_strictImplicitLeftBracket = _init_l_Lean_Parser_Term_strictImplicitLeftBracket();
lean_mark_persistent(l_Lean_Parser_Term_strictImplicitLeftBracket);
l_Lean_Parser_Term_strictImplicitRightBracket = _init_l_Lean_Parser_Term_strictImplicitRightBracket();
lean_mark_persistent(l_Lean_Parser_Term_strictImplicitRightBracket);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_optIdent = _init_l_Lean_Parser_Term_optIdent();
lean_mark_persistent(l_Lean_Parser_Term_optIdent);
l_Lean_Parser_Term_instBinder = _init_l_Lean_Parser_Term_instBinder();
lean_mark_persistent(l_Lean_Parser_Term_instBinder);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_typeSpec = _init_l_Lean_Parser_Term_typeSpec();
lean_mark_persistent(l_Lean_Parser_Term_typeSpec);
l_Lean_Parser_Term_optType = _init_l_Lean_Parser_Term_optType();
lean_mark_persistent(l_Lean_Parser_Term_optType);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_optEllipsis = _init_l_Lean_Parser_Term_optEllipsis();
lean_mark_persistent(l_Lean_Parser_Term_optEllipsis);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_structInstArrayRef = _init_l_Lean_Parser_Term_structInstArrayRef();
lean_mark_persistent(l_Lean_Parser_Term_structInstArrayRef);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_structInstLVal = _init_l_Lean_Parser_Term_structInstLVal();
lean_mark_persistent(l_Lean_Parser_Term_structInstLVal);
l_Lean_Parser_Term_structInstFieldBinder = _init_l_Lean_Parser_Term_structInstFieldBinder();
lean_mark_persistent(l_Lean_Parser_Term_structInstFieldBinder);
l_Lean_Parser_Term_optTypeForStructInst = _init_l_Lean_Parser_Term_optTypeForStructInst();
lean_mark_persistent(l_Lean_Parser_Term_optTypeForStructInst);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_structInstField = _init_l_Lean_Parser_Term_structInstField();
lean_mark_persistent(l_Lean_Parser_Term_structInstField);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM = _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM();
lean_mark_persistent(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Attr(uint8_t builtin);
lean_object* initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Doc(uint8_t builtin);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Term_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
