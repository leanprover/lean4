// Lean compiler output
// Module: Lean.Parser.Term.Basic
// Imports: public import Lean.Parser.Attr public import Lean.Parser.Level public import Lean.Parser.Term.Doc meta import Lean.Parser.Basic
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "`sepByIndentSemicolon(p)` parses a sequence of `p` optionally followed by `;`,\nsimilar to `manyIndent(p \";\"\?)`, except that if two occurrences of `p` occur on the same line,\nthe `;` is mandatory. This is used by tactic parsing, so that\n```\nexample := by\n  skip\n  skip\n```\nis legal, but `by skip skip` is not - it must be written as `by skip; skip`. "};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 363, .m_capacity = 363, .m_length = 362, .m_data = "`sepBy1IndentSemicolon(p)` parses a (nonempty) sequence of `p` optionally followed by `;`,\nsimilar to `many1Indent(p \";\"\?)`, except that if two occurrences of `p` occur on the same line,\nthe `;` is mandatory. This is used by tactic parsing, so that\n```\nexample := by\n  skip\n  skip\n```\nis legal, but `by skip skip` is not - it must be written as `by skip; skip`. "};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 133, .m_capacity = 133, .m_length = 131, .m_data = "The syntax `{ tacs }` is an alternative syntax for `· tacs`.\nIt runs the tactics in sequence, and fails if the goal is not solved. "};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 166, .m_capacity = 166, .m_length = 165, .m_data = "A sequence of tactics in brackets, or a delimiter-free indented sequence of tactics.\nDelimiter-free indentation is determined by the *first* tactic of the sequence. "};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 257, .m_capacity = 257, .m_length = 256, .m_data = "Same as [`tacticSeq`] but requires delimiter-free tactic sequence to have strict indentation.\nFalls back to an empty tactic sequence when no appropriately indented content follows, producing\nan elaboration error (unsolved goals) rather than a parse error. "};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 814, .m_capacity = 814, .m_length = 813, .m_data = "A *hole* (or *placeholder term*), which stands for an unknown term that is expected to be inferred based on context.\nFor example, in `@id _ Nat.zero`, the `_` must be the type of `Nat.zero`, which is `Nat`.\n\nThe way this works is that holes create fresh metavariables.\nThe elaborator is allowed to assign terms to metavariables while it is checking definitional equalities.\nThis is often known as *unification*.\n\nNormally, all holes must be solved for. However, there are a few contexts where this is not necessary:\n* In `match` patterns, holes are catch-all patterns.\n* In some tactics, such as `refine'` and `apply`, unsolved-for placeholders become new goals.\n\nRelated concept: implicit parameters are automatically filled in with holes during the elaboration process.\n\nSee also `\?m` syntax (synthetic holes).\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3166, .m_capacity = 3166, .m_length = 3151, .m_data = "A *synthetic hole* (or *synthetic placeholder*), which stands for an unknown term that should be synthesized using tactics.\n- `\?_` creates a fresh metavariable with an auto-generated name.\n- `\?m` either refers to a pre-existing metavariable named `m` or creates a fresh metavariable with that name.\n\nIn particular, the synthetic hole syntax creates \"synthetic opaque metavariables\",\nthe same kind of metavariable used to represent goals in the tactic state.\n\nSynthetic holes are similar to holes in that `_` also creates metavariables,\nbut synthetic opaque metavariables have some different properties:\n- In tactics such as `refine`, only synthetic holes yield new goals.\n- During elaboration, unification will not solve for synthetic opaque metavariables, they are \"opaque\".\n  This is to prevent counterintuitive behavior such as disappearing goals.\n- When synthetic holes appear under binders, they capture local variables using a more complicated mechanism known as delayed assignment.\n\n## Delayed assigned metavariables\n\nThis section gives an overview of some technical details of synthetic holes, which you should feel free to skip.\nUnderstanding delayed assignments is mainly useful for those who are working on tactics and other metaprogramming.\nIt is included here until there is a suitable place for it in the reference manual.\n\nWhen a synthetic hole appears under a binding construct, such as for example `fun (x : α) (y : β) => \?s`,\nthe system creates a *delayed assignment*. This consists of\n1. A metavariable `\?m` of type `(x : α) → (y : β) → γ x y` whose local context is the local context outside the `fun`,\n  where `γ x y` is the type of `\?s`. Recall that `x` and `y` appear in the local context of `\?s`.\n2. A delayed assignment record associating `\?m` to `\?s` and the variables `#[x, y]` in the local context of `\?s`\n\nThen, this function elaborates as `fun (x : α) (y : β) => \?m x y`, where one should understand `x` and `y` here\nas being De Bruijn indexes, since Lean uses the locally nameless encoding of lambda calculus.\n\nOnce `\?s` is fully solved for, in the sense that after metavariable instantiation it is a metavariable-free term `e`,\nthen we can make the assignment `\?m := fun (x' : α) (y' : β) => e[x := x', y := y']`.\n(Implementation note: Lean only instantiates full applications `\?m x' y'` of delayed assigned metavariables, to skip forming this function.)\nThis delayed assignment mechanism is essential to the operation of basic tactics like `intro`,\nand a good mental model is that it is a way to \"apply\" the metavariable `\?s` by substituting values in for some of its local variables.\nWhile it would be easier to immediately assign `\?s := \?m x y`,\ndelayed assignment preserves `\?s` as an unsolved-for metavariable with a local context that still contains `x` and `y`,\nwhich is exactly what tactics like `intro` need.\n\nBy default, delayed assigned metavariables pretty print with what they are delayed assigned to.\nThe delayed assigned metavariables themselves can be pretty printed using `set_option pp.mvars.delayed true`.\n\nFor more information, see the \"Gruesome details\" module docstrings in `Lean.MetavarContext`.\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 435, .m_capacity = 435, .m_length = 428, .m_data = "The `⋯` term denotes a term that was omitted by the pretty printer.\nThe presence of `⋯` in pretty printer output is controlled by the `pp.deepTerms` and `pp.proofs` options,\nand these options can be further adjusted using `pp.deepTerms.threshold` and `pp.proofs.threshold`.\n\nIt is only meant to be used for pretty printing.\nHowever, in case it is copied and pasted from the Infoview, `⋯` logs a warning and elaborates like `_`.\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 147, .m_capacity = 147, .m_length = 146, .m_data = "Explicit binder, like `(x y : A)` or `(x y)`.\nDefault values can be specified using `(x : A := v)` syntax, and tactics using `(x : A := by tac)`.\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 379, .m_capacity = 379, .m_length = 378, .m_data = "Implicit binder, like `{x y : A}` or `{x y}`.\nIn regular applications, whenever all parameters before it have been specified,\nthen a `_` placeholder is automatically inserted for this parameter.\nImplicit parameters should be able to be determined from the other arguments and the return type\nby unification.\n\nIn `@` explicit mode, implicit binders behave like explicit binders.\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 783, .m_capacity = 783, .m_length = 752, .m_data = "Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`.\nIn contrast to `{ ... }` implicit binders, strict-implicit binders do not automatically insert\na `_` placeholder until at least one subsequent explicit parameter is specified.\nDo *not* use strict-implicit binders unless there is a subsequent explicit parameter.\nAssuming this rule is followed, for fully applied expressions implicit and strict-implicit binders have the same behavior.\n\nExample: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`,\nthen `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter,\nand `h hs` has type `p y`.\nIn contrast, if `h' : ∀ {x : A}, x ∈ s → p x`, then `h` by itself elaborates to have type `\?m ∈ s → p \?m`\nwith `\?m` a fresh metavariable.\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 430, .m_capacity = 430, .m_length = 429, .m_data = "Instance-implicit binder, like `[C]` or `[inst : C]`.\nIn regular applications without `@` explicit mode, it is automatically inserted\nand solved for by typeclass inference for the specified class `C`.\nIn `@` explicit mode, if `_` is used for an instance-implicit parameter, then it is still solved for by typeclass inference;\nuse `(_)` to inhibit this and have it be solved for by unification instead, like an implicit argument.\n"};
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
static const lean_string_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 328, .m_capacity = 328, .m_length = 323, .m_data = "A `bracketedBinder` matches any kind of binder group that uses some kind of brackets:\n* An explicit binder like `(x y : A)`\n* An implicit binder like `{x y : A}`\n* A strict implicit binder, `⦃y z : A⦄` or its ASCII alternative `{{y z : A}}`\n* An instance binder `[A]` or `[x : A]` (multiple variables are not allowed here)\n"};
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_(){
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
lean_dec_ref(v___x_84_);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_();
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser(lean_object* v_rbp_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_92_ = l_Lean_Parser_categoryParser(v___x_91_, v_rbp_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_convParser(lean_object* v_rbp_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Parser_convParser___closed__1));
v___x_98_ = l_Lean_Parser_categoryParser(v___x_97_, v_rbp_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter(lean_object* v_p_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1));
v___x_109_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_102_, v___x_108_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___boxed(lean_object* v_p_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter(v_p_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer(lean_object* v_p_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; 
v___x_125_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_126_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0));
v___x_127_ = 1;
v___x_128_ = l_Lean_Parser_sepByIndent_parenthesizer(v_p_119_, v___x_125_, v___x_126_, v___x_127_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___boxed(lean_object* v_p_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer(v_p_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_135_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_137_ = l_Lean_Parser_symbol(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__3));
v___x_143_ = l_Lean_Parser_symbol(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5));
v___x_146_ = l_Lean_Parser_checkColGe(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__5));
v___x_148_ = l_Lean_Parser_checkColEq(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__8));
v___x_151_ = l_Lean_Parser_checkLinebreakBefore(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = l_Lean_Parser_pushNone;
v___x_153_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__9);
v___x_154_ = l_Lean_Parser_andthen(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__10);
v___x_156_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__7);
v___x_157_ = l_Lean_Parser_andthen(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__11);
v___x_159_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__0);
v___x_160_ = l_Lean_Parser_orelse(v___x_159_, v___x_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon(lean_object* v_p_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_p_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_162_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_163_ = 1;
v___x_164_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2));
v___x_165_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4);
v_p_166_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_164_, v_p_161_, v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6);
v___x_168_ = l_Lean_Parser_andthen(v___x_167_, v_p_166_);
v___x_169_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12);
v___x_170_ = l_Lean_Parser_sepBy(v___x_168_, v___x_162_, v___x_169_, v___x_163_);
v___x_171_ = l_Lean_Parser_withPosition(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
v___x_182_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3));
v___x_183_ = l_Lean_addBuiltinDocString(v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(lean_object* v_p_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__1));
v___x_193_ = l_Lean_Parser_sepByIndent_formatter___redArg(v_p_186_, v___x_192_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed(lean_object* v_p_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(v_p_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(lean_object* v_p_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_207_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_208_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___closed__0));
v___x_209_ = 1;
v___x_210_ = l_Lean_Parser_sepBy1Indent_parenthesizer(v_p_201_, v___x_207_, v___x_208_, v___x_209_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed(lean_object* v_p_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(v_p_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon(lean_object* v_p_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_p_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_219_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___closed__0));
v___x_220_ = 1;
v___x_221_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__2));
v___x_222_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__4);
v_p_223_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_221_, v_p_218_, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__6);
v___x_225_ = l_Lean_Parser_andthen(v___x_224_, v_p_223_);
v___x_226_ = lean_obj_once(&l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12, &l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12_once, _init_l_Lean_Parser_Tactic_sepByIndentSemicolon___closed__12);
v___x_227_ = l_Lean_Parser_sepBy1(v___x_225_, v___x_219_, v___x_226_, v___x_220_);
v___x_228_ = l_Lean_Parser_withPosition(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
v___x_238_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2));
v___x_239_ = l_Lean_addBuiltinDocString(v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___y_281_; lean_object* v___x_291_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_276_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
v___x_277_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_279_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_291_ = l_Lean_Parser_registerAlias(v___x_275_, v___x_276_, v___x_277_, v___x_278_, v___x_279_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref(v___x_291_);
v___x_292_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_293_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_275_, v___x_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v___x_293_);
v___x_294_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_295_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_275_, v___x_294_);
v___y_281_ = v___x_295_;
goto v___jp_280_;
}
else
{
v___y_281_ = v___x_293_;
goto v___jp_280_;
}
}
else
{
v___y_281_ = v___x_291_;
goto v___jp_280_;
}
v___jp_280_:
{
if (lean_obj_tag(v___y_281_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v___y_281_);
v___x_282_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_283_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
v___x_284_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_285_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_286_ = l_Lean_Parser_registerAlias(v___x_282_, v___x_283_, v___x_284_, v___x_285_, v___x_279_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec_ref(v___x_286_);
v___x_287_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_288_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_282_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec_ref(v___x_288_);
v___x_289_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_290_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_282_, v___x_289_);
return v___x_290_;
}
else
{
return v___x_288_;
}
}
else
{
return v___x_286_;
}
}
else
{
return v___y_281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2____boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
return v_res_297_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2(void){
_start:
{
uint8_t v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_304_ = 0;
v___x_305_ = 1;
v___x_306_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_307_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0));
v___x_308_ = l_Lean_Parser_mkAntiquot(v___x_307_, v___x_306_, v___x_305_, v___x_304_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_311_ = l_Lean_Parser_categoryParser(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_313_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4);
v___x_315_ = lean_unsigned_to_nat(1024u);
v___x_316_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_317_ = l_Lean_Parser_leadingNode(v___x_316_, v___x_315_, v___x_314_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5);
v___x_319_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2);
v___x_320_ = l_Lean_Parser_withAntiquot(v___x_319_, v___x_318_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6);
v___x_322_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_323_ = l_Lean_Parser_withCache(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2(void){
_start:
{
uint8_t v___x_331_; uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = 0;
v___x_332_ = 1;
v___x_333_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_334_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0));
v___x_335_ = l_Lean_Parser_mkAntiquot(v___x_334_, v___x_333_, v___x_332_, v___x_331_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3));
v___x_338_ = l_Lean_Parser_symbol(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_340_ = l_Lean_Parser_Tactic_sepByIndentSemicolon(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_343_ = l_Lean_Parser_symbol(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_345_ = l_Lean_Parser_skip;
v___x_346_ = l_Lean_Parser_andthen(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8);
v___x_348_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5);
v___x_349_ = l_Lean_Parser_andthen(v___x_348_, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9);
v___x_351_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4);
v___x_352_ = l_Lean_Parser_andthen(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10);
v___x_354_ = lean_unsigned_to_nat(1024u);
v___x_355_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_356_ = l_Lean_Parser_leadingNode(v___x_355_, v___x_354_, v___x_353_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11);
v___x_358_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2);
v___x_359_ = l_Lean_Parser_withAntiquot(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12);
v___x_361_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_362_ = l_Lean_Parser_withCache(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed(void){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1(){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_367_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0));
v___x_368_ = l_Lean_addBuiltinDocString(v___x_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___boxed(lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg(lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_377_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_376_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg___boxed(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter(lean_object* v_rbp_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_385_, v_a_386_, v_a_387_, v_a_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___boxed(lean_object* v_rbp_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Parser_tacticParser_formatter(v_rbp_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_rbp_391_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_412_ = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter___boxed), 6, 1);
lean_closure_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_416_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4);
v___x_417_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_417_, 0, v___x_416_);
lean_closure_set(v___x_417_, 1, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6);
v___x_419_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__3));
v___x_420_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_420_, 0, v___x_419_);
lean_closure_set(v___x_420_, 1, v___x_418_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7);
v___x_422_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__1));
v___x_423_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_423_, 0, v___x_422_);
lean_closure_set(v___x_423_, 1, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8);
v___x_425_ = lean_unsigned_to_nat(1024u);
v___x_426_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_427_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_427_, 0, v___x_426_);
lean_closure_set(v___x_427_, 1, v___x_425_);
lean_closure_set(v___x_427_, 2, v___x_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__0));
v___x_434_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9);
v___x_435_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_433_, v___x_434_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed(lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_451_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_452_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1));
v___x_453_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_454_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_450_, v___x_451_, v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0));
v___x_476_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2));
v___x_477_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_475_, v___x_476_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed(lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9(){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_492_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_493_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0));
v___x_494_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_495_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_491_, v___x_492_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___boxed(lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
return v_res_497_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_512_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_513_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_513_, 0, v___x_512_);
lean_closure_set(v___x_513_, 1, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3, &l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3);
v___x_515_ = lean_unsigned_to_nat(1024u);
v___x_516_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_517_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_517_, 0, v___x_516_);
lean_closure_set(v___x_517_, 1, v___x_515_);
lean_closure_set(v___x_517_, 2, v___x_514_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter(lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_524_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4);
v___x_525_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_523_, v___x_524_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___boxed(lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Parser_Tactic_tacticSeq_formatter(v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13(){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_540_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_541_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0));
v___x_542_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_543_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_539_, v___x_540_, v___x_541_, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___boxed(lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer(lean_object* v_rbp_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_553_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_552_, v_rbp_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer___boxed(lean_object* v_rbp_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Parser_tacticParser_parenthesizer(v_rbp_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__0));
v___x_598_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__10));
v___x_599_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_597_, v___x_598_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed(lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19(){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_614_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_615_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_616_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1));
v___x_617_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_614_, v___x_615_, v___x_616_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___boxed(lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0));
v___x_640_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2));
v___x_641_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_639_, v___x_640_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed(lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23(){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_655_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_656_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_657_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0));
v___x_658_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_659_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_655_, v___x_656_, v___x_657_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___boxed(lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
return v_res_661_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_670_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_671_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_671_, 0, v___x_670_);
lean_closure_set(v___x_671_, 1, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1);
v___x_673_ = lean_unsigned_to_nat(1024u);
v___x_674_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_675_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_675_, 0, v___x_674_);
lean_closure_set(v___x_675_, 1, v___x_673_);
lean_closure_set(v___x_675_, 2, v___x_672_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer(lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_682_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2, &l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2);
v___x_683_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_681_, v___x_682_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed(lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Parser_Tactic_tacticSeq_parenthesizer(v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27(){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_697_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_698_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_699_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0));
v___x_700_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___x_701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_697_, v___x_698_, v___x_699_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___boxed(lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
return v_res_703_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__0(void){
_start:
{
uint8_t v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = 0;
v___x_705_ = 1;
v___x_706_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_707_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0));
v___x_708_ = l_Lean_Parser_mkAntiquot(v___x_707_, v___x_706_, v___x_705_, v___x_704_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__1(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_710_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_711_ = l_Lean_Parser_orelse(v___x_710_, v___x_709_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__2(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__1, &l_Lean_Parser_Tactic_tacticSeq___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__1);
v___x_713_ = lean_unsigned_to_nat(1024u);
v___x_714_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_715_ = l_Lean_Parser_leadingNode(v___x_714_, v___x_713_, v___x_712_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__3(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__2, &l_Lean_Parser_Tactic_tacticSeq___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__2);
v___x_717_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_718_ = l_Lean_Parser_withAntiquot(v___x_717_, v___x_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__4(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__3, &l_Lean_Parser_Tactic_tacticSeq___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__3);
v___x_720_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_721_ = l_Lean_Parser_withCache(v___x_720_, v___x_719_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__4, &l_Lean_Parser_Tactic_tacticSeq___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__4);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1(){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_726_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0));
v___x_727_ = l_Lean_addBuiltinDocString(v___x_725_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_732_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_733_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_733_, 0, v___x_732_);
lean_closure_set(v___x_733_, 1, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2));
v___x_738_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1);
v___x_739_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_739_, 0, v___x_738_);
lean_closure_set(v___x_739_, 1, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3);
v___x_741_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_742_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_742_, 0, v___x_741_);
lean_closure_set(v___x_742_, 1, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4);
v___x_744_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_745_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_745_, 0, v___x_744_);
lean_closure_set(v___x_745_, 1, v___x_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_752_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5);
v___x_753_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_751_, v___x_752_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3(){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_768_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_769_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_770_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1));
v___x_771_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed), 5, 0);
v___x_772_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_768_, v___x_769_, v___x_770_, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___boxed(lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
return v_res_774_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_777_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_778_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_778_, 0, v___x_777_);
lean_closure_set(v___x_778_, 1, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2));
v___x_783_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1);
v___x_784_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_784_, 0, v___x_783_);
lean_closure_set(v___x_784_, 1, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3);
v___x_786_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_787_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_787_, 0, v___x_786_);
lean_closure_set(v___x_787_, 1, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4);
v___x_789_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_790_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_790_, 0, v___x_789_);
lean_closure_set(v___x_790_, 1, v___x_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_797_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5);
v___x_798_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_796_, v___x_797_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7(){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_812_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_813_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_814_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0));
v___x_815_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed), 5, 0);
v___x_816_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_812_, v___x_813_, v___x_814_, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___boxed(lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
return v_res_818_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0));
v___x_821_ = l_Lean_Parser_checkColGt(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_823_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1);
v___x_824_ = l_Lean_Parser_andthen(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = l_Lean_Parser_pushNone;
v___x_826_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_827_ = l_Lean_Parser_node(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3);
v___x_829_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2);
v___x_830_ = l_Lean_Parser_orelse(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4);
v___x_832_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_833_ = l_Lean_Parser_orelse(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5);
v___x_835_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_836_ = l_Lean_Parser_node(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6);
v___x_838_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_839_ = l_Lean_Parser_withAntiquot(v___x_838_, v___x_837_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt(void){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1(){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0));
v___x_849_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1));
v___x_850_ = l_Lean_addBuiltinDocString(v___x_848_, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___boxed(lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter(lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_874_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__4));
v___x_875_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_873_, v___x_874_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter___boxed(lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Parser_Tactic_seq1_formatter(v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3(){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_889_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_890_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_891_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0));
v___x_892_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_formatter___boxed), 5, 0);
v___x_893_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_889_, v___x_890_, v___x_891_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___boxed(lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer(lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_910_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1));
v___x_911_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_909_, v___x_910_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___boxed(lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Parser_Tactic_seq1_parenthesizer(v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7(){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_925_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_926_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_927_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0));
v___x_928_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_parenthesizer___boxed), 5, 0);
v___x_929_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_925_, v___x_926_, v___x_927_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___boxed(lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
return v_res_931_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__0(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_933_ = l_Lean_Parser_symbol(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__1(void){
_start:
{
uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_934_ = 1;
v___x_935_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__0, &l_Lean_Parser_Tactic_seq1___closed__0_once, _init_l_Lean_Parser_Tactic_seq1___closed__0);
v___x_936_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_937_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_938_ = l_Lean_Parser_sepBy1(v___x_937_, v___x_936_, v___x_935_, v___x_934_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__2(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__1, &l_Lean_Parser_Tactic_seq1___closed__1_once, _init_l_Lean_Parser_Tactic_seq1___closed__1);
v___x_940_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_941_ = l_Lean_Parser_node(v___x_940_, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__2, &l_Lean_Parser_Tactic_seq1___closed__2_once, _init_l_Lean_Parser_Tactic_seq1___closed__2);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__2(void){
_start:
{
uint8_t v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_949_ = 0;
v___x_950_ = 1;
v___x_951_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_952_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__0));
v___x_953_ = l_Lean_Parser_mkAntiquot(v___x_952_, v___x_951_, v___x_950_, v___x_949_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__4(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__3));
v___x_956_ = l_Lean_Parser_symbol(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__5(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_957_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_958_ = lean_unsigned_to_nat(1024u);
v___x_959_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_960_ = l_Lean_Parser_leadingNode(v___x_959_, v___x_958_, v___x_957_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__6(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__5, &l_Lean_Parser_Term_hole___closed__5_once, _init_l_Lean_Parser_Term_hole___closed__5);
v___x_962_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__2, &l_Lean_Parser_Term_hole___closed__2_once, _init_l_Lean_Parser_Term_hole___closed__2);
v___x_963_ = l_Lean_Parser_withAntiquot(v___x_962_, v___x_961_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__7(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__6, &l_Lean_Parser_Term_hole___closed__6_once, _init_l_Lean_Parser_Term_hole___closed__6);
v___x_965_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_966_ = l_Lean_Parser_withCache(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__7, &l_Lean_Parser_Term_hole___closed__7_once, _init_l_Lean_Parser_Term_hole___closed__7);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1(){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_973_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_974_ = l_Lean_Parser_Term_hole;
v___x_975_ = lean_unsigned_to_nat(1000u);
v___x_976_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_972_, v___x_973_, v___x_974_, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___boxed(lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3(){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_982_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0));
v___x_983_ = l_Lean_addBuiltinDocString(v___x_981_, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___boxed(lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5(){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1013_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6));
v___x_1014_ = l_Lean_addBuiltinDeclarationRanges(v___x_1012_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___boxed(lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter(lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__0));
v___x_1036_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__2));
v___x_1037_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1035_, v___x_1036_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Parser_Term_hole_formatter(v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9(){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1051_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1052_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1053_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0));
v___x_1054_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1055_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1051_, v___x_1052_, v___x_1053_, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___boxed(lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer(lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__0));
v___x_1077_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__2));
v___x_1078_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1076_, v___x_1077_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Parser_Term_hole_parenthesizer(v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13(){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1092_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1093_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1094_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0));
v___x_1095_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1096_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1092_, v___x_1093_, v___x_1094_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___boxed(lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
return v_res_1098_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__2(void){
_start:
{
uint8_t v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1105_ = 0;
v___x_1106_ = 1;
v___x_1107_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1108_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__0));
v___x_1109_ = l_Lean_Parser_mkAntiquot(v___x_1108_, v___x_1107_, v___x_1106_, v___x_1105_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__4(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__3));
v___x_1112_ = l_Lean_Parser_symbol(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_1114_ = l_Lean_Parser_ident;
v___x_1115_ = l_Lean_Parser_orelse(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__6(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__5, &l_Lean_Parser_Term_syntheticHole___closed__5_once, _init_l_Lean_Parser_Term_syntheticHole___closed__5);
v___x_1117_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__4, &l_Lean_Parser_Term_syntheticHole___closed__4_once, _init_l_Lean_Parser_Term_syntheticHole___closed__4);
v___x_1118_ = l_Lean_Parser_andthen(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__7(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__6, &l_Lean_Parser_Term_syntheticHole___closed__6_once, _init_l_Lean_Parser_Term_syntheticHole___closed__6);
v___x_1120_ = lean_unsigned_to_nat(1024u);
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1122_ = l_Lean_Parser_leadingNode(v___x_1121_, v___x_1120_, v___x_1119_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__8(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__7, &l_Lean_Parser_Term_syntheticHole___closed__7_once, _init_l_Lean_Parser_Term_syntheticHole___closed__7);
v___x_1124_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__2, &l_Lean_Parser_Term_syntheticHole___closed__2_once, _init_l_Lean_Parser_Term_syntheticHole___closed__2);
v___x_1125_ = l_Lean_Parser_withAntiquot(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__9(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__8, &l_Lean_Parser_Term_syntheticHole___closed__8_once, _init_l_Lean_Parser_Term_syntheticHole___closed__8);
v___x_1127_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1128_ = l_Lean_Parser_withCache(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole(void){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__9, &l_Lean_Parser_Term_syntheticHole___closed__9_once, _init_l_Lean_Parser_Term_syntheticHole___closed__9);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1(){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1132_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1133_ = l_Lean_Parser_Term_syntheticHole;
v___x_1134_ = lean_unsigned_to_nat(1000u);
v___x_1135_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1131_, v___x_1132_, v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1___boxed(lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3(){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1141_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0));
v___x_1142_ = l_Lean_addBuiltinDocString(v___x_1140_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___boxed(lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5(){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1172_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6));
v___x_1173_ = l_Lean_addBuiltinDeclarationRanges(v___x_1171_, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___boxed(lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter(lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__0));
v___x_1202_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__5));
v___x_1203_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1201_, v___x_1202_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter___boxed(lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Parser_Term_syntheticHole_formatter(v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9(){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1217_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1218_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1219_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0));
v___x_1220_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_formatter___boxed), 5, 0);
v___x_1221_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1217_, v___x_1218_, v___x_1219_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___boxed(lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer(lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0));
v___x_1250_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5));
v___x_1251_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1249_, v___x_1250_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed(lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Parser_Term_syntheticHole_parenthesizer(v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13(){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1265_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1266_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1267_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0));
v___x_1268_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed), 5, 0);
v___x_1269_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1265_, v___x_1266_, v___x_1267_, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___boxed(lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
return v_res_1271_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__2(void){
_start:
{
uint8_t v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1278_ = 0;
v___x_1279_ = 1;
v___x_1280_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1281_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__0));
v___x_1282_ = l_Lean_Parser_mkAntiquot(v___x_1281_, v___x_1280_, v___x_1279_, v___x_1278_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__4(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__3));
v___x_1285_ = l_Lean_Parser_symbol(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__5(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__4, &l_Lean_Parser_Term_omission___closed__4_once, _init_l_Lean_Parser_Term_omission___closed__4);
v___x_1287_ = lean_unsigned_to_nat(1024u);
v___x_1288_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1289_ = l_Lean_Parser_leadingNode(v___x_1288_, v___x_1287_, v___x_1286_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__6(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__5, &l_Lean_Parser_Term_omission___closed__5_once, _init_l_Lean_Parser_Term_omission___closed__5);
v___x_1291_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__2, &l_Lean_Parser_Term_omission___closed__2_once, _init_l_Lean_Parser_Term_omission___closed__2);
v___x_1292_ = l_Lean_Parser_withAntiquot(v___x_1291_, v___x_1290_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__7(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__6, &l_Lean_Parser_Term_omission___closed__6_once, _init_l_Lean_Parser_Term_omission___closed__6);
v___x_1294_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1295_ = l_Lean_Parser_withCache(v___x_1294_, v___x_1293_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission(void){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__7, &l_Lean_Parser_Term_omission___closed__7_once, _init_l_Lean_Parser_Term_omission___closed__7);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1(){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1299_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1300_ = l_Lean_Parser_Term_omission;
v___x_1301_ = lean_unsigned_to_nat(1000u);
v___x_1302_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1298_, v___x_1299_, v___x_1300_, v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1___boxed(lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3(){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1308_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0));
v___x_1309_ = l_Lean_addBuiltinDocString(v___x_1307_, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5(){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1339_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6));
v___x_1340_ = l_Lean_addBuiltinDeclarationRanges(v___x_1338_, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___boxed(lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter(lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__0));
v___x_1362_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__2));
v___x_1363_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1361_, v___x_1362_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter___boxed(lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Parser_Term_omission_formatter(v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9(){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1377_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1378_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1379_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0));
v___x_1380_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_formatter___boxed), 5, 0);
v___x_1381_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1377_, v___x_1378_, v___x_1379_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___boxed(lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer(lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__0));
v___x_1403_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__2));
v___x_1404_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1402_, v___x_1403_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer___boxed(lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Parser_Term_omission_parenthesizer(v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13(){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1418_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1419_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1420_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0));
v___x_1421_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_parenthesizer___boxed), 5, 0);
v___x_1422_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1418_, v___x_1419_, v___x_1420_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_1431_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1432_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1430_, v___x_1431_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter___boxed(lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Parser_Term_binderIdent_formatter(v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_1445_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1446_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_1444_, v___x_1445_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer___boxed(lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Parser_Term_binderIdent_parenthesizer(v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
return v_res_1452_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent___closed__0(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lean_Parser_Term_hole;
v___x_1454_ = l_Lean_Parser_ident;
v___x_1455_ = l_Lean_Parser_orelse(v___x_1454_, v___x_1453_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent(void){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_obj_once(&l_Lean_Parser_Term_binderIdent___closed__0, &l_Lean_Parser_Term_binderIdent___closed__0_once, _init_l_Lean_Parser_Term_binderIdent___closed__0);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter(uint8_t v_requireType_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
if (v_requireType_1468_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1475_ = l_Lean_Parser_optional_formatter(v___x_1474_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1477_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1478_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1476_, v___x_1477_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter___boxed(lean_object* v_requireType_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
uint8_t v_requireType_boxed_1485_; lean_object* v_res_1486_; 
v_requireType_boxed_1485_ = lean_unbox(v_requireType_1479_);
v_res_1486_ = l_Lean_Parser_Term_binderType_formatter(v_requireType_boxed_1485_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer(uint8_t v_requireType_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
if (v_requireType_1494_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1501_ = l_Lean_Parser_optional_parenthesizer(v___x_1500_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1503_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1504_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1502_, v___x_1503_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer___boxed(lean_object* v_requireType_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
uint8_t v_requireType_boxed_1511_; lean_object* v_res_1512_; 
v_requireType_boxed_1511_ = lean_unbox(v_requireType_1505_);
v_res_1512_ = l_Lean_Parser_Term_binderType_parenthesizer(v_requireType_boxed_1511_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
return v_res_1512_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__0(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__0));
v___x_1514_ = l_Lean_Parser_symbol(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = l_Lean_Parser_termParser(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__2(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1518_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1519_ = l_Lean_Parser_andthen(v___x_1518_, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__3(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1521_ = l_Lean_Parser_optional(v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__4(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1523_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1524_ = l_Lean_Parser_node(v___x_1523_, v___x_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType(uint8_t v_requireType_1525_){
_start:
{
if (v_requireType_1525_ == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__3, &l_Lean_Parser_Term_binderType___closed__3_once, _init_l_Lean_Parser_Term_binderType___closed__3);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__4, &l_Lean_Parser_Term_binderType___closed__4_once, _init_l_Lean_Parser_Term_binderType___closed__4);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType___boxed(lean_object* v_requireType_1528_){
_start:
{
uint8_t v_requireType_boxed_1529_; lean_object* v_res_1530_; 
v_requireType_boxed_1529_ = lean_unbox(v_requireType_1528_);
v_res_1530_ = l_Lean_Parser_Term_binderType(v_requireType_boxed_1529_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_1556_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__8));
v___x_1557_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1557_, 0, v___x_1556_);
lean_closure_set(v___x_1557_, 1, v___x_1555_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1558_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__9, &l_Lean_Parser_Term_binderTactic_formatter___closed__9_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9);
v___x_1559_ = lean_unsigned_to_nat(1024u);
v___x_1560_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1561_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1561_, 0, v___x_1560_);
lean_closure_set(v___x_1561_, 1, v___x_1559_);
lean_closure_set(v___x_1561_, 2, v___x_1558_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter(lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__2));
v___x_1568_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__10, &l_Lean_Parser_Term_binderTactic_formatter___closed__10_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10);
v___x_1569_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1567_, v___x_1568_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter___boxed(lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Parser_Term_binderTactic_formatter(v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3(){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1583_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1584_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1585_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0));
v___x_1586_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_1587_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1583_, v___x_1584_, v___x_1585_, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___boxed(lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_1590_, v___x_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed(lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(v___x_1598_, v___x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1605_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___f_1621_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3));
v___x_1622_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1622_, 0, v___f_1621_);
lean_closure_set(v___x_1622_, 1, v___x_1620_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1623_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4);
v___x_1624_ = lean_unsigned_to_nat(1024u);
v___x_1625_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1626_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1626_, 0, v___x_1625_);
lean_closure_set(v___x_1626_, 1, v___x_1624_);
lean_closure_set(v___x_1626_, 2, v___x_1623_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer(lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0));
v___x_1633_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5);
v___x_1634_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1632_, v___x_1633_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___boxed(lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Parser_Term_binderTactic_parenthesizer(v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7(){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1649_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1650_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0));
v___x_1651_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_1652_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1648_, v___x_1649_, v___x_1650_, v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___boxed(lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
return v_res_1654_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__0(void){
_start:
{
uint8_t v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1655_ = 0;
v___x_1656_ = 1;
v___x_1657_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1658_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__0));
v___x_1659_ = l_Lean_Parser_mkAntiquot(v___x_1658_, v___x_1657_, v___x_1656_, v___x_1655_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__1(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__3));
v___x_1661_ = l_Lean_Parser_symbol(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__2(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__5));
v___x_1663_ = l_Lean_Parser_symbol(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__3(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__2, &l_Lean_Parser_Term_binderTactic___closed__2_once, _init_l_Lean_Parser_Term_binderTactic___closed__2);
v___x_1665_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1666_ = l_Lean_Parser_andthen(v___x_1665_, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__4(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__3, &l_Lean_Parser_Term_binderTactic___closed__3_once, _init_l_Lean_Parser_Term_binderTactic___closed__3);
v___x_1668_ = l_Lean_Parser_atomic(v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__5(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_1670_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__4, &l_Lean_Parser_Term_binderTactic___closed__4_once, _init_l_Lean_Parser_Term_binderTactic___closed__4);
v___x_1671_ = l_Lean_Parser_andthen(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__6(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1672_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__5, &l_Lean_Parser_Term_binderTactic___closed__5_once, _init_l_Lean_Parser_Term_binderTactic___closed__5);
v___x_1673_ = lean_unsigned_to_nat(1024u);
v___x_1674_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1675_ = l_Lean_Parser_leadingNode(v___x_1674_, v___x_1673_, v___x_1672_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__7(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__6, &l_Lean_Parser_Term_binderTactic___closed__6_once, _init_l_Lean_Parser_Term_binderTactic___closed__6);
v___x_1677_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__0, &l_Lean_Parser_Term_binderTactic___closed__0_once, _init_l_Lean_Parser_Term_binderTactic___closed__0);
v___x_1678_ = l_Lean_Parser_withAntiquot(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__8(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__7, &l_Lean_Parser_Term_binderTactic___closed__7_once, _init_l_Lean_Parser_Term_binderTactic___closed__7);
v___x_1680_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1681_ = l_Lean_Parser_withCache(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__8, &l_Lean_Parser_Term_binderTactic___closed__8_once, _init_l_Lean_Parser_Term_binderTactic___closed__8);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__2(void){
_start:
{
uint8_t v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1689_ = 0;
v___x_1690_ = 1;
v___x_1691_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1692_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__0));
v___x_1693_ = l_Lean_Parser_mkAntiquot(v___x_1692_, v___x_1691_, v___x_1690_, v___x_1689_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__3(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1695_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1696_ = l_Lean_Parser_andthen(v___x_1695_, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__4(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1697_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__3, &l_Lean_Parser_Term_binderDefault___closed__3_once, _init_l_Lean_Parser_Term_binderDefault___closed__3);
v___x_1698_ = lean_unsigned_to_nat(1024u);
v___x_1699_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1700_ = l_Lean_Parser_leadingNode(v___x_1699_, v___x_1698_, v___x_1697_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__5(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__4, &l_Lean_Parser_Term_binderDefault___closed__4_once, _init_l_Lean_Parser_Term_binderDefault___closed__4);
v___x_1702_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__2, &l_Lean_Parser_Term_binderDefault___closed__2_once, _init_l_Lean_Parser_Term_binderDefault___closed__2);
v___x_1703_ = l_Lean_Parser_withAntiquot(v___x_1702_, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__6(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__5, &l_Lean_Parser_Term_binderDefault___closed__5_once, _init_l_Lean_Parser_Term_binderDefault___closed__5);
v___x_1705_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1706_ = l_Lean_Parser_withCache(v___x_1705_, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault(void){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__6, &l_Lean_Parser_Term_binderDefault___closed__6_once, _init_l_Lean_Parser_Term_binderDefault___closed__6);
return v___x_1707_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM(void){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Parser_Term_binderDefault;
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v_stxTrav_1712_; lean_object* v_cur_1713_; lean_object* v___x_1714_; 
v___x_1711_ = lean_st_ref_get(v___y_1709_);
v_stxTrav_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_stxTrav_1712_);
lean_dec(v___x_1711_);
v_cur_1713_ = lean_ctor_get(v_stxTrav_1712_, 0);
lean_inc(v_cur_1713_);
lean_dec_ref(v_stxTrav_1712_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_cur_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1715_);
lean_dec(v___y_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1719_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___boxed(lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v___x_1736_);
v___x_1737_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_1732_);
return v___x_1737_;
}
else
{
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed(lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer(lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v_a_1757_; lean_object* v___y_1759_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1756_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v_a_1752_);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc_n(v_a_1757_, 2);
lean_dec_ref(v___x_1756_);
v___x_1762_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1763_ = l_Lean_Syntax_isOfKind(v_a_1757_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_dec(v_a_1757_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___y_1759_ = v___x_1764_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = l_Lean_Syntax_getArg(v_a_1757_, v___x_1765_);
lean_dec(v_a_1757_);
v___x_1767_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1));
v___x_1768_ = l_Lean_Syntax_isOfKind(v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_unsigned_to_nat(0u);
v___y_1759_ = v___x_1769_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Parser_maxPrec;
v___y_1759_ = v___x_1770_;
goto v___jp_1758_;
}
}
v___jp_1758_:
{
lean_object* v___f_1760_; lean_object* v___x_1761_; 
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1760_, 0, v___y_1759_);
v___x_1761_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___f_1760_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___boxed(lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Parser_Term_binderDefault_parenthesizer(v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1776_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1783_ = 0;
v___x_1784_ = 1;
v___x_1785_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1786_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__0));
v___x_1787_ = l_Lean_Parser_mkAntiquot(v___x_1786_, v___x_1785_, v___x_1784_, v___x_1783_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__3));
v___x_1790_ = l_Lean_Parser_symbol(v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__5(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = l_Lean_Parser_Term_binderIdent;
v___x_1792_ = l_Lean_Parser_many1(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__6(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = l_Lean_Parser_Term_binderDefault;
v___x_1794_ = l_Lean_Parser_Term_binderTactic;
v___x_1795_ = l_Lean_Parser_orelse(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__7(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__6, &l_Lean_Parser_Term_explicitBinder___closed__6_once, _init_l_Lean_Parser_Term_explicitBinder___closed__6);
v___x_1797_ = l_Lean_Parser_optional(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__9(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__8));
v___x_1800_ = l_Lean_Parser_symbol(v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder(uint8_t v_requireType_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1802_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1803_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__2, &l_Lean_Parser_Term_explicitBinder___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder___closed__2);
v___x_1804_ = lean_unsigned_to_nat(1024u);
v___x_1805_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__4, &l_Lean_Parser_Term_explicitBinder___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder___closed__4);
v___x_1806_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1807_ = l_Lean_Parser_Term_binderType(v_requireType_1801_);
v___x_1808_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__7, &l_Lean_Parser_Term_explicitBinder___closed__7_once, _init_l_Lean_Parser_Term_explicitBinder___closed__7);
v___x_1809_ = l_Lean_Parser_andthen(v___x_1807_, v___x_1808_);
v___x_1810_ = l_Lean_Parser_andthen(v___x_1806_, v___x_1809_);
v___x_1811_ = l_Lean_Parser_withoutPosition(v___x_1810_);
v___x_1812_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__9, &l_Lean_Parser_Term_explicitBinder___closed__9_once, _init_l_Lean_Parser_Term_explicitBinder___closed__9);
v___x_1813_ = l_Lean_Parser_andthen(v___x_1811_, v___x_1812_);
v___x_1814_ = l_Lean_Parser_andthen(v___x_1805_, v___x_1813_);
v___x_1815_ = l_Lean_Parser_leadingNode(v___x_1802_, v___x_1804_, v___x_1814_);
v___x_1816_ = l_Lean_Parser_withAntiquot(v___x_1803_, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___boxed(lean_object* v_requireType_1817_){
_start:
{
uint8_t v_requireType_boxed_1818_; lean_object* v_res_1819_; 
v_requireType_boxed_1818_ = lean_unbox(v_requireType_1817_);
v_res_1819_ = l_Lean_Parser_Term_explicitBinder(v_requireType_boxed_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1(){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1823_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0));
v___x_1824_ = l_Lean_addBuiltinDocString(v___x_1822_, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___boxed(lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
return v_res_1826_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1833_ = 0;
v___x_1834_ = 1;
v___x_1835_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1836_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__0));
v___x_1837_ = l_Lean_Parser_mkAntiquot(v___x_1836_, v___x_1835_, v___x_1834_, v___x_1833_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__3));
v___x_1840_ = l_Lean_Parser_symbol(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder(uint8_t v_requireType_1841_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1842_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1843_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__2, &l_Lean_Parser_Term_implicitBinder___closed__2_once, _init_l_Lean_Parser_Term_implicitBinder___closed__2);
v___x_1844_ = lean_unsigned_to_nat(1024u);
v___x_1845_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1846_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1847_ = l_Lean_Parser_Term_binderType(v_requireType_1841_);
v___x_1848_ = l_Lean_Parser_andthen(v___x_1846_, v___x_1847_);
v___x_1849_ = l_Lean_Parser_withoutPosition(v___x_1848_);
v___x_1850_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1851_ = l_Lean_Parser_andthen(v___x_1849_, v___x_1850_);
v___x_1852_ = l_Lean_Parser_andthen(v___x_1845_, v___x_1851_);
v___x_1853_ = l_Lean_Parser_leadingNode(v___x_1842_, v___x_1844_, v___x_1852_);
v___x_1854_ = l_Lean_Parser_withAntiquot(v___x_1843_, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___boxed(lean_object* v_requireType_1855_){
_start:
{
uint8_t v_requireType_boxed_1856_; lean_object* v_res_1857_; 
v_requireType_boxed_1856_ = lean_unbox(v_requireType_1855_);
v_res_1857_ = l_Lean_Parser_Term_implicitBinder(v_requireType_boxed_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1(){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1861_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0));
v___x_1862_ = l_Lean_addBuiltinDocString(v___x_1860_, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
return v_res_1864_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1866_ = l_Lean_Parser_andthen(v___x_1865_, v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0);
v___x_1871_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1872_ = l_Lean_Parser_node(v___x_1871_, v___x_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3);
v___x_1874_ = l_Lean_Parser_atomic(v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5));
v___x_1877_ = l_Lean_Parser_symbol(v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6);
v___x_1879_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4);
v___x_1880_ = l_Lean_Parser_orelse(v___x_1879_, v___x_1878_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket(void){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1883_ = l_Lean_Parser_andthen(v___x_1882_, v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__0, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0);
v___x_1885_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1886_ = l_Lean_Parser_node(v___x_1885_, v___x_1884_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__1, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1);
v___x_1888_ = l_Lean_Parser_atomic(v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket___closed__3));
v___x_1891_ = l_Lean_Parser_symbol(v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__4, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4);
v___x_1893_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__2, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2);
v___x_1894_ = l_Lean_Parser_orelse(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket(void){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__5, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__5_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = 0;
v___x_1903_ = 1;
v___x_1904_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1905_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__0));
v___x_1906_ = l_Lean_Parser_mkAntiquot(v___x_1905_, v___x_1904_, v___x_1903_, v___x_1902_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder(uint8_t v_requireType_1907_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1908_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1909_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitBinder___closed__2, &l_Lean_Parser_Term_strictImplicitBinder___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2);
v___x_1910_ = lean_unsigned_to_nat(1024u);
v___x_1911_ = l_Lean_Parser_Term_strictImplicitLeftBracket;
v___x_1912_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1913_ = l_Lean_Parser_Term_binderType(v_requireType_1907_);
v___x_1914_ = l_Lean_Parser_Term_strictImplicitRightBracket;
v___x_1915_ = l_Lean_Parser_andthen(v___x_1913_, v___x_1914_);
v___x_1916_ = l_Lean_Parser_andthen(v___x_1912_, v___x_1915_);
v___x_1917_ = l_Lean_Parser_andthen(v___x_1911_, v___x_1916_);
v___x_1918_ = l_Lean_Parser_leadingNode(v___x_1908_, v___x_1910_, v___x_1917_);
v___x_1919_ = l_Lean_Parser_withAntiquot(v___x_1909_, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___boxed(lean_object* v_requireType_1920_){
_start:
{
uint8_t v_requireType_boxed_1921_; lean_object* v_res_1922_; 
v_requireType_boxed_1921_ = lean_unbox(v_requireType_1920_);
v_res_1922_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_boxed_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1(){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1926_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0));
v___x_1927_ = l_Lean_addBuiltinDocString(v___x_1925_, v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___boxed(lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
return v_res_1929_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__0(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1931_ = l_Lean_Parser_ident;
v___x_1932_ = l_Lean_Parser_andthen(v___x_1931_, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__0, &l_Lean_Parser_Term_optIdent___closed__0_once, _init_l_Lean_Parser_Term_optIdent___closed__0);
v___x_1934_ = l_Lean_Parser_atomic(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__2(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__1, &l_Lean_Parser_Term_optIdent___closed__1_once, _init_l_Lean_Parser_Term_optIdent___closed__1);
v___x_1936_ = l_Lean_Parser_optional(v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent(void){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__2, &l_Lean_Parser_Term_optIdent___closed__2_once, _init_l_Lean_Parser_Term_optIdent___closed__2);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__2(void){
_start:
{
uint8_t v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1944_ = 0;
v___x_1945_ = 1;
v___x_1946_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1947_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__0));
v___x_1948_ = l_Lean_Parser_mkAntiquot(v___x_1947_, v___x_1946_, v___x_1945_, v___x_1944_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__4(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__3));
v___x_1951_ = l_Lean_Parser_symbol(v___x_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__5(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1953_ = l_Lean_Parser_Term_optIdent;
v___x_1954_ = l_Lean_Parser_andthen(v___x_1953_, v___x_1952_);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__6(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__5, &l_Lean_Parser_Term_instBinder___closed__5_once, _init_l_Lean_Parser_Term_instBinder___closed__5);
v___x_1956_ = l_Lean_Parser_withoutPosition(v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__8(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__7));
v___x_1959_ = l_Lean_Parser_symbol(v___x_1958_);
return v___x_1959_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__9(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_1961_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__6, &l_Lean_Parser_Term_instBinder___closed__6_once, _init_l_Lean_Parser_Term_instBinder___closed__6);
v___x_1962_ = l_Lean_Parser_andthen(v___x_1961_, v___x_1960_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__10(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__9, &l_Lean_Parser_Term_instBinder___closed__9_once, _init_l_Lean_Parser_Term_instBinder___closed__9);
v___x_1964_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_1965_ = l_Lean_Parser_andthen(v___x_1964_, v___x_1963_);
return v___x_1965_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__11(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1966_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__10, &l_Lean_Parser_Term_instBinder___closed__10_once, _init_l_Lean_Parser_Term_instBinder___closed__10);
v___x_1967_ = lean_unsigned_to_nat(1024u);
v___x_1968_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1969_ = l_Lean_Parser_leadingNode(v___x_1968_, v___x_1967_, v___x_1966_);
return v___x_1969_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__12(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__11, &l_Lean_Parser_Term_instBinder___closed__11_once, _init_l_Lean_Parser_Term_instBinder___closed__11);
v___x_1971_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__2, &l_Lean_Parser_Term_instBinder___closed__2_once, _init_l_Lean_Parser_Term_instBinder___closed__2);
v___x_1972_ = l_Lean_Parser_withAntiquot(v___x_1971_, v___x_1970_);
return v___x_1972_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__13(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1973_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__12, &l_Lean_Parser_Term_instBinder___closed__12_once, _init_l_Lean_Parser_Term_instBinder___closed__12);
v___x_1974_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1975_ = l_Lean_Parser_withCache(v___x_1974_, v___x_1973_);
return v___x_1975_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder(void){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__13, &l_Lean_Parser_Term_instBinder___closed__13_once, _init_l_Lean_Parser_Term_instBinder___closed__13);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1(){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1980_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0));
v___x_1981_ = l_Lean_addBuiltinDocString(v___x_1979_, v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___boxed(lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter(lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__0));
v___x_2004_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__2));
v___x_2005_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2003_, v___x_2004_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter___boxed(lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Parser_Term_binderDefault_formatter(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3(){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2019_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2020_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_2021_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0));
v___x_2022_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2023_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2019_, v___x_2020_, v___x_2021_, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___boxed(lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter___boxed), 6, 1);
lean_closure_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2038_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_2039_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2039_, 0, v___x_2038_);
lean_closure_set(v___x_2039_, 1, v___x_2037_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__3, &l_Lean_Parser_Term_explicitBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3);
v___x_2041_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter(uint8_t v_requireType_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2050_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2051_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__0));
v___x_2052_ = lean_unsigned_to_nat(1024u);
v___x_2053_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__1));
v___x_2054_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2055_ = lean_box(v_requireType_2044_);
v___x_2056_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2056_, 0, v___x_2055_);
v___x_2057_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__4, &l_Lean_Parser_Term_explicitBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4);
v___x_2058_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2058_, 0, v___x_2056_);
lean_closure_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2059_, 0, v___x_2054_);
lean_closure_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2060_, 0, v___x_2059_);
v___x_2061_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__5));
v___x_2062_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2062_, 0, v___x_2060_);
lean_closure_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2063_, 0, v___x_2053_);
lean_closure_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2064_, 0, v___x_2063_);
v___x_2065_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2065_, 0, v___x_2050_);
lean_closure_set(v___x_2065_, 1, v___x_2052_);
lean_closure_set(v___x_2065_, 2, v___x_2064_);
v___x_2066_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2051_, v___x_2065_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter___boxed(lean_object* v_requireType_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
uint8_t v_requireType_boxed_2073_; lean_object* v_res_2074_; 
v_requireType_boxed_2073_ = lean_unbox(v_requireType_2067_);
v_res_2074_ = l_Lean_Parser_Term_explicitBinder_formatter(v_requireType_boxed_2073_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3));
v___x_2091_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4));
v___x_2092_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2090_, v___x_2091_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed(lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter(lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2));
v___x_2113_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3));
v___x_2114_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2112_, v___x_2113_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed(lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Parser_Term_strictImplicitRightBracket_formatter(v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter(uint8_t v_requireType_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2134_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2135_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0));
v___x_2136_ = lean_unsigned_to_nat(1024u);
v___x_2137_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed), 5, 0);
v___x_2138_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2139_ = lean_box(v_requireType_2128_);
v___x_2140_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2140_, 0, v___x_2139_);
v___x_2141_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed), 5, 0);
v___x_2142_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2142_, 0, v___x_2140_);
lean_closure_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2143_, 0, v___x_2138_);
lean_closure_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2144_, 0, v___x_2137_);
lean_closure_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2145_, 0, v___x_2144_);
v___x_2146_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2146_, 0, v___x_2134_);
lean_closure_set(v___x_2146_, 1, v___x_2136_);
lean_closure_set(v___x_2146_, 2, v___x_2145_);
v___x_2147_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2135_, v___x_2146_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed(lean_object* v_requireType_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
uint8_t v_requireType_boxed_2154_; lean_object* v_res_2155_; 
v_requireType_boxed_2154_ = lean_unbox(v_requireType_2148_);
v_res_2155_ = l_Lean_Parser_Term_strictImplicitBinder_formatter(v_requireType_boxed_2154_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter(uint8_t v_requireType_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2169_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2170_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_formatter___closed__0));
v___x_2171_ = lean_unsigned_to_nat(1024u);
v___x_2172_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0));
v___x_2173_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2174_ = lean_box(v_requireType_2163_);
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2175_, 0, v___x_2174_);
v___x_2176_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2176_, 0, v___x_2173_);
lean_closure_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2177_, 0, v___x_2176_);
v___x_2178_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_2179_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2179_, 0, v___x_2177_);
lean_closure_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2180_, 0, v___x_2172_);
lean_closure_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2181_, 0, v___x_2180_);
v___x_2182_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2182_, 0, v___x_2169_);
lean_closure_set(v___x_2182_, 1, v___x_2171_);
lean_closure_set(v___x_2182_, 2, v___x_2181_);
v___x_2183_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2170_, v___x_2182_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter___boxed(lean_object* v_requireType_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
uint8_t v_requireType_boxed_2190_; lean_object* v_res_2191_; 
v_requireType_boxed_2190_ = lean_unbox(v_requireType_2184_);
v_res_2191_ = l_Lean_Parser_Term_implicitBinder_formatter(v_requireType_boxed_2190_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter(lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_formatter___closed__1));
v___x_2203_ = l_Lean_Parser_optional_formatter(v___x_2202_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter___boxed(lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Parser_Term_optIdent_formatter(v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2209_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__2));
v___x_2220_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_formatter___boxed), 5, 0);
v___x_2221_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2221_, 0, v___x_2220_);
lean_closure_set(v___x_2221_, 1, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__2, &l_Lean_Parser_Term_instBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__2);
v___x_2223_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__5(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__4));
v___x_2227_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__3, &l_Lean_Parser_Term_instBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__3);
v___x_2228_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2228_, 0, v___x_2227_);
lean_closure_set(v___x_2228_, 1, v___x_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__6(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__5, &l_Lean_Parser_Term_instBinder_formatter___closed__5_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__5);
v___x_2230_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__1));
v___x_2231_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2231_, 0, v___x_2230_);
lean_closure_set(v___x_2231_, 1, v___x_2229_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__7(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__6, &l_Lean_Parser_Term_instBinder_formatter___closed__6_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__6);
v___x_2233_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__8(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__7, &l_Lean_Parser_Term_instBinder_formatter___closed__7_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__7);
v___x_2235_ = lean_unsigned_to_nat(1024u);
v___x_2236_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2237_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2237_, 0, v___x_2236_);
lean_closure_set(v___x_2237_, 1, v___x_2235_);
lean_closure_set(v___x_2237_, 2, v___x_2234_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter(lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__0));
v___x_2244_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__8, &l_Lean_Parser_Term_instBinder_formatter___closed__8_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__8);
v___x_2245_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2243_, v___x_2244_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter___boxed(lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Parser_Term_instBinder_formatter(v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19(){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2259_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2260_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2261_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0));
v___x_2262_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2263_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2259_, v___x_2260_, v___x_2261_, v___x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___boxed(lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter(uint8_t v_requireType_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2284_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__2));
v___x_2285_ = lean_box(v_requireType_2278_);
v___x_2286_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2286_, 0, v___x_2285_);
v___x_2287_ = lean_box(v_requireType_2278_);
v___x_2288_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2288_, 0, v___x_2287_);
v___x_2289_ = lean_box(v_requireType_2278_);
v___x_2290_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2292_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2292_, 0, v___x_2290_);
lean_closure_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2293_, 0, v___x_2288_);
lean_closure_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2294_, 0, v___x_2286_);
lean_closure_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2284_, v___x_2294_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object* v_requireType_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
uint8_t v_requireType_boxed_2302_; lean_object* v_res_2303_; 
v_requireType_boxed_2302_ = lean_unbox(v_requireType_2296_);
v_res_2303_ = l_Lean_Parser_Term_bracketedBinder_formatter(v_requireType_boxed_2302_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2303_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_2314_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___boxed), 5, 0);
v___x_2316_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_2317_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2317_, 0, v___x_2316_);
lean_closure_set(v___x_2317_, 1, v___x_2315_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3);
v___x_2319_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer(uint8_t v_requireType_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2328_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2329_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0));
v___x_2330_ = lean_unsigned_to_nat(1024u);
v___x_2331_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1));
v___x_2332_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2333_ = lean_box(v_requireType_2322_);
v___x_2334_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2334_, 0, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4);
v___x_2336_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2336_, 0, v___x_2334_);
lean_closure_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2337_, 0, v___x_2332_);
lean_closure_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2338_, 0, v___x_2337_);
v___x_2339_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5));
v___x_2340_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2340_, 0, v___x_2338_);
lean_closure_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2341_, 0, v___x_2331_);
lean_closure_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2342_, 0, v___x_2341_);
v___x_2343_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2343_, 0, v___x_2328_);
lean_closure_set(v___x_2343_, 1, v___x_2330_);
lean_closure_set(v___x_2343_, 2, v___x_2342_);
v___x_2344_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2329_, v___x_2343_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed(lean_object* v_requireType_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
uint8_t v_requireType_boxed_2351_; lean_object* v_res_2352_; 
v_requireType_boxed_2351_ = lean_unbox(v_requireType_2345_);
v_res_2352_ = l_Lean_Parser_Term_explicitBinder_parenthesizer(v_requireType_boxed_2351_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(lean_object* v___x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Parser_group_parenthesizer(v___x_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed(lean_object* v___x_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(v___x_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___f_2380_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2));
v___x_2381_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3));
v___x_2382_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2380_, v___x_2381_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed(lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___f_2400_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1));
v___x_2401_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2));
v___x_2402_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2400_, v___x_2401_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed(lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(uint8_t v_requireType_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2422_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2423_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0));
v___x_2424_ = lean_unsigned_to_nat(1024u);
v___x_2425_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed), 5, 0);
v___x_2426_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2427_ = lean_box(v_requireType_2416_);
v___x_2428_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2428_, 0, v___x_2427_);
v___x_2429_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed), 5, 0);
v___x_2430_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2430_, 0, v___x_2428_);
lean_closure_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2431_, 0, v___x_2426_);
lean_closure_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2432_, 0, v___x_2425_);
lean_closure_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2433_, 0, v___x_2432_);
v___x_2434_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2434_, 0, v___x_2422_);
lean_closure_set(v___x_2434_, 1, v___x_2424_);
lean_closure_set(v___x_2434_, 2, v___x_2433_);
v___x_2435_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2423_, v___x_2434_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed(lean_object* v_requireType_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
uint8_t v_requireType_boxed_2442_; lean_object* v_res_2443_; 
v_requireType_boxed_2442_ = lean_unbox(v_requireType_2436_);
v_res_2443_ = l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(v_requireType_boxed_2442_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer(uint8_t v_requireType_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2457_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2458_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0));
v___x_2459_ = lean_unsigned_to_nat(1024u);
v___x_2460_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0));
v___x_2461_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2462_ = lean_box(v_requireType_2451_);
v___x_2463_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2463_, 0, v___x_2462_);
v___x_2464_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2464_, 0, v___x_2461_);
lean_closure_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2465_, 0, v___x_2464_);
v___x_2466_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6));
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2467_, 0, v___x_2465_);
lean_closure_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2468_, 0, v___x_2460_);
lean_closure_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2469_, 0, v___x_2468_);
v___x_2470_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2470_, 0, v___x_2457_);
lean_closure_set(v___x_2470_, 1, v___x_2459_);
lean_closure_set(v___x_2470_, 2, v___x_2469_);
v___x_2471_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2458_, v___x_2470_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed(lean_object* v_requireType_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
uint8_t v_requireType_boxed_2478_; lean_object* v_res_2479_; 
v_requireType_boxed_2478_ = lean_unbox(v_requireType_2472_);
v_res_2479_ = l_Lean_Parser_Term_implicitBinder_parenthesizer(v_requireType_boxed_2478_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer(lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v___f_2488_; lean_object* v___x_2489_; 
v___f_2488_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_parenthesizer___closed__0));
v___x_2489_ = l_Lean_Parser_optional_parenthesizer(v___f_2488_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer___boxed(lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Parser_Term_optIdent_parenthesizer(v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
return v_res_2495_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__1));
v___x_2506_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_parenthesizer___boxed), 5, 0);
v___x_2507_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2507_, 0, v___x_2506_);
lean_closure_set(v___x_2507_, 1, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2);
v___x_2509_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__4));
v___x_2513_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3);
v___x_2514_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2514_, 0, v___x_2513_);
lean_closure_set(v___x_2514_, 1, v___x_2512_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__5, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5);
v___x_2516_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__1));
v___x_2517_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2517_, 0, v___x_2516_);
lean_closure_set(v___x_2517_, 1, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__6, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__6_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6);
v___x_2519_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2520_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__7, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7);
v___x_2521_ = lean_unsigned_to_nat(1024u);
v___x_2522_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2523_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2523_, 0, v___x_2522_);
lean_closure_set(v___x_2523_, 1, v___x_2521_);
lean_closure_set(v___x_2523_, 2, v___x_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer(lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__0));
v___x_2530_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__8, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8);
v___x_2531_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2529_, v___x_2530_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___boxed(lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Parser_Term_instBinder_parenthesizer(v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37(){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2545_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2546_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2547_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0));
v___x_2548_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2549_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2545_, v___x_2546_, v___x_2547_, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___boxed(lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer(uint8_t v_requireType_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2564_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0));
v___x_2565_ = lean_box(v_requireType_2558_);
v___x_2566_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2566_, 0, v___x_2565_);
v___x_2567_ = lean_box(v_requireType_2558_);
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2568_, 0, v___x_2567_);
v___x_2569_ = lean_box(v_requireType_2558_);
v___x_2570_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2570_, 0, v___x_2569_);
v___x_2571_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2572_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2572_, 0, v___x_2570_);
lean_closure_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2573_, 0, v___x_2568_);
lean_closure_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2574_, 0, v___x_2566_);
lean_closure_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2564_, v___x_2574_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object* v_requireType_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
uint8_t v_requireType_boxed_2582_; lean_object* v_res_2583_; 
v_requireType_boxed_2582_ = lean_unbox(v_requireType_2576_);
v_res_2583_ = l_Lean_Parser_Term_bracketedBinder_parenthesizer(v_requireType_boxed_2582_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2583_;
}
}
static lean_object* _init_l_Lean_Parser_Term_bracketedBinder___closed__0(void){
_start:
{
uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2584_ = 1;
v___x_2585_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2586_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__0));
v___x_2587_ = l_Lean_Parser_mkAntiquot(v___x_2586_, v___x_2585_, v___x_2584_, v___x_2584_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t v_requireType_2588_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2589_ = lean_obj_once(&l_Lean_Parser_Term_bracketedBinder___closed__0, &l_Lean_Parser_Term_bracketedBinder___closed__0_once, _init_l_Lean_Parser_Term_bracketedBinder___closed__0);
v___x_2590_ = l_Lean_Parser_Term_explicitBinder(v_requireType_2588_);
v___x_2591_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_2588_);
v___x_2592_ = l_Lean_Parser_Term_implicitBinder(v_requireType_2588_);
v___x_2593_ = l_Lean_Parser_Term_instBinder;
v___x_2594_ = l_Lean_Parser_orelse(v___x_2592_, v___x_2593_);
v___x_2595_ = l_Lean_Parser_orelse(v___x_2591_, v___x_2594_);
v___x_2596_ = l_Lean_Parser_orelse(v___x_2590_, v___x_2595_);
v___x_2597_ = l_Lean_Parser_withAntiquot(v___x_2589_, v___x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___boxed(lean_object* v_requireType_2598_){
_start:
{
uint8_t v_requireType_boxed_2599_; lean_object* v_res_2600_; 
v_requireType_boxed_2599_ = lean_unbox(v_requireType_2598_);
v_res_2600_ = l_Lean_Parser_Term_bracketedBinder(v_requireType_boxed_2599_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1(){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2604_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0));
v___x_2605_ = l_Lean_addBuiltinDocString(v___x_2603_, v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___boxed(lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter(lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__2));
v___x_2631_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__3));
v___x_2632_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2630_, v___x_2631_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter___boxed(lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Parser_Term_typeSpec_formatter(v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3(){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2646_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2647_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2648_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0));
v___x_2649_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2650_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2646_, v___x_2647_, v___x_2648_, v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___boxed(lean_object* v_a_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer(lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0));
v___x_2670_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1));
v___x_2671_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2669_, v___x_2670_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___boxed(lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_Parser_Term_typeSpec_parenthesizer(v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7(){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2685_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2686_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2687_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0));
v___x_2688_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2685_, v___x_2686_, v___x_2687_, v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___boxed(lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
return v_res_2691_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__0(void){
_start:
{
uint8_t v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2692_ = 0;
v___x_2693_ = 1;
v___x_2694_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2695_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__0));
v___x_2696_ = l_Lean_Parser_mkAntiquot(v___x_2695_, v___x_2694_, v___x_2693_, v___x_2692_);
return v___x_2696_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__1(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2697_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_2698_ = lean_unsigned_to_nat(1024u);
v___x_2699_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2700_ = l_Lean_Parser_leadingNode(v___x_2699_, v___x_2698_, v___x_2697_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__2(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__1, &l_Lean_Parser_Term_typeSpec___closed__1_once, _init_l_Lean_Parser_Term_typeSpec___closed__1);
v___x_2702_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__0, &l_Lean_Parser_Term_typeSpec___closed__0_once, _init_l_Lean_Parser_Term_typeSpec___closed__0);
v___x_2703_ = l_Lean_Parser_withAntiquot(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__3(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__2, &l_Lean_Parser_Term_typeSpec___closed__2_once, _init_l_Lean_Parser_Term_typeSpec___closed__2);
v___x_2705_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2706_ = l_Lean_Parser_withCache(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec(void){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__3, &l_Lean_Parser_Term_typeSpec___closed__3_once, _init_l_Lean_Parser_Term_typeSpec___closed__3);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter(lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2714_ = l_Lean_Parser_optional_formatter(v___x_2713_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter___boxed(lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Parser_Term_optType_formatter(v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer(lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2727_ = l_Lean_Parser_optional_parenthesizer(v___x_2726_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer___boxed(lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Parser_Term_optType_parenthesizer(v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
return v_res_2733_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType___closed__0(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = l_Lean_Parser_Term_typeSpec;
v___x_2735_ = l_Lean_Parser_optional(v___x_2734_);
return v___x_2735_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType(void){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_obj_once(&l_Lean_Parser_Term_optType___closed__0, &l_Lean_Parser_Term_optType___closed__0_once, _init_l_Lean_Parser_Term_optType___closed__0);
return v___x_2736_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = lean_unsigned_to_nat(2382944618u);
v___x_2768_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2769_ = l_Lean_Name_num___override(v___x_2768_, v___x_2767_);
return v___x_2769_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2771_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2772_ = l_Lean_Name_str___override(v___x_2771_, v___x_2770_);
return v___x_2772_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2774_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2775_ = l_Lean_Name_str___override(v___x_2774_, v___x_2773_);
return v___x_2775_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_unsigned_to_nat(2u);
v___x_2777_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2778_ = l_Lean_Name_num___override(v___x_2777_, v___x_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2780_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2781_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2782_ = 0;
v___x_2783_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2784_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_2780_, v___x_2781_, v___x_2782_, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2____boxed(lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser(lean_object* v_rbp_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_2791_ = l_Lean_Parser_categoryParser(v___x_2790_, v_rbp_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter(lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__2));
v___x_2820_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__6));
v___x_2821_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2819_, v___x_2820_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter___boxed(lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_Parser_Term_optEllipsis_formatter(v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3(){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2835_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2836_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2837_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0));
v___x_2838_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_formatter___boxed), 5, 0);
v___x_2839_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2835_, v___x_2836_, v___x_2837_, v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___boxed(lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer(lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0));
v___x_2863_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3));
v___x_2864_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2862_, v___x_2863_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed(lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Parser_Term_optEllipsis_parenthesizer(v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7(){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2878_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2879_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2880_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0));
v___x_2881_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed), 5, 0);
v___x_2882_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2878_, v___x_2879_, v___x_2880_, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___boxed(lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
return v_res_2884_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__0(void){
_start:
{
uint8_t v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2885_ = 0;
v___x_2886_ = 1;
v___x_2887_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2888_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__0));
v___x_2889_ = l_Lean_Parser_mkAntiquot(v___x_2888_, v___x_2887_, v___x_2886_, v___x_2885_);
return v___x_2889_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__1(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__3));
v___x_2891_ = l_Lean_Parser_symbol(v___x_2890_);
return v___x_2891_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__2(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__1, &l_Lean_Parser_Term_optEllipsis___closed__1_once, _init_l_Lean_Parser_Term_optEllipsis___closed__1);
v___x_2893_ = l_Lean_Parser_optional(v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__3(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2894_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__2, &l_Lean_Parser_Term_optEllipsis___closed__2_once, _init_l_Lean_Parser_Term_optEllipsis___closed__2);
v___x_2895_ = lean_unsigned_to_nat(1024u);
v___x_2896_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2897_ = l_Lean_Parser_leadingNode(v___x_2896_, v___x_2895_, v___x_2894_);
return v___x_2897_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__4(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__3, &l_Lean_Parser_Term_optEllipsis___closed__3_once, _init_l_Lean_Parser_Term_optEllipsis___closed__3);
v___x_2899_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__0, &l_Lean_Parser_Term_optEllipsis___closed__0_once, _init_l_Lean_Parser_Term_optEllipsis___closed__0);
v___x_2900_ = l_Lean_Parser_withAntiquot(v___x_2899_, v___x_2898_);
return v___x_2900_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__5(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__4, &l_Lean_Parser_Term_optEllipsis___closed__4_once, _init_l_Lean_Parser_Term_optEllipsis___closed__4);
v___x_2902_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2903_ = l_Lean_Parser_withCache(v___x_2902_, v___x_2901_);
return v___x_2903_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis(void){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__5, &l_Lean_Parser_Term_optEllipsis___closed__5_once, _init_l_Lean_Parser_Term_optEllipsis___closed__5);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter(lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2));
v___x_2936_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6));
v___x_2937_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2935_, v___x_2936_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___boxed(lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Parser_Term_structInstArrayRef_formatter(v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3(){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2951_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2952_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_2953_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0));
v___x_2954_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_2955_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2951_, v___x_2952_, v___x_2953_, v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___boxed(lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer(lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0));
v___x_2983_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4));
v___x_2984_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2982_, v___x_2983_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed(lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Parser_Term_structInstArrayRef_parenthesizer(v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7(){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2998_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2999_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3000_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0));
v___x_3001_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3002_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2998_, v___x_2999_, v___x_3000_, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___boxed(lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
return v_res_3004_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__0(void){
_start:
{
uint8_t v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3005_ = 0;
v___x_3006_ = 1;
v___x_3007_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3008_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0));
v___x_3009_ = l_Lean_Parser_mkAntiquot(v___x_3008_, v___x_3007_, v___x_3006_, v___x_3005_);
return v___x_3009_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__1(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_3011_ = l_Lean_Parser_withoutPosition(v___x_3010_);
return v___x_3011_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__2(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_3013_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__1, &l_Lean_Parser_Term_structInstArrayRef___closed__1_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__1);
v___x_3014_ = l_Lean_Parser_andthen(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__3(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__2, &l_Lean_Parser_Term_structInstArrayRef___closed__2_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__2);
v___x_3016_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_3017_ = l_Lean_Parser_andthen(v___x_3016_, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__4(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3018_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__3, &l_Lean_Parser_Term_structInstArrayRef___closed__3_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__3);
v___x_3019_ = lean_unsigned_to_nat(1024u);
v___x_3020_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3021_ = l_Lean_Parser_leadingNode(v___x_3020_, v___x_3019_, v___x_3018_);
return v___x_3021_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__5(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__4, &l_Lean_Parser_Term_structInstArrayRef___closed__4_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__4);
v___x_3023_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__0, &l_Lean_Parser_Term_structInstArrayRef___closed__0_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__0);
v___x_3024_ = l_Lean_Parser_withAntiquot(v___x_3023_, v___x_3022_);
return v___x_3024_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__6(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__5, &l_Lean_Parser_Term_structInstArrayRef___closed__5_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__5);
v___x_3026_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3027_ = l_Lean_Parser_withCache(v___x_3026_, v___x_3025_);
return v___x_3027_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef(void){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__6, &l_Lean_Parser_Term_structInstArrayRef___closed__6_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__6);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3043_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3044_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3044_, 0, v___x_3043_);
lean_closure_set(v___x_3044_, 1, v___x_3042_);
return v___x_3044_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__3, &l_Lean_Parser_Term_structInstLVal_formatter___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3);
v___x_3046_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3047_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3047_, 0, v___x_3046_);
lean_closure_set(v___x_3047_, 1, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3052_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3053_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3053_, 0, v___x_3052_);
lean_closure_set(v___x_3053_, 1, v___x_3051_);
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__7, &l_Lean_Parser_Term_structInstLVal_formatter___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7);
v___x_3055_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__6));
v___x_3056_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3056_, 0, v___x_3055_);
lean_closure_set(v___x_3056_, 1, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__8, &l_Lean_Parser_Term_structInstLVal_formatter___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8);
v___x_3058_ = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter___boxed), 6, 1);
lean_closure_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3060_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__9, &l_Lean_Parser_Term_structInstLVal_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9);
v___x_3061_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3061_, 0, v___x_3060_);
lean_closure_set(v___x_3061_, 1, v___x_3059_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__10, &l_Lean_Parser_Term_structInstLVal_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10);
v___x_3063_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3063_, 0, v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__11, &l_Lean_Parser_Term_structInstLVal_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11);
v___x_3065_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__4, &l_Lean_Parser_Term_structInstLVal_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4);
v___x_3066_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3066_, 0, v___x_3065_);
lean_closure_set(v___x_3066_, 1, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__12, &l_Lean_Parser_Term_structInstLVal_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12);
v___x_3068_ = lean_unsigned_to_nat(1024u);
v___x_3069_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3070_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3070_, 0, v___x_3069_);
lean_closure_set(v___x_3070_, 1, v___x_3068_);
lean_closure_set(v___x_3070_, 2, v___x_3067_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter(lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__2));
v___x_3077_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__13, &l_Lean_Parser_Term_structInstLVal_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13);
v___x_3078_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3076_, v___x_3077_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter___boxed(lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Parser_Term_structInstLVal_formatter(v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3(){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3092_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3093_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3094_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0));
v___x_3095_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3096_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3092_, v___x_3093_, v___x_3094_, v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___boxed(lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_3100_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0___boxed(lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3110_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___f_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___f_3120_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0));
v___x_3121_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3121_, 0, v___f_3120_);
lean_closure_set(v___x_3121_, 1, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2);
v___x_3123_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_3124_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3124_, 0, v___x_3123_);
lean_closure_set(v___x_3124_, 1, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3136_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7));
v___x_3137_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3137_, 0, v___x_3136_);
lean_closure_set(v___x_3137_, 1, v___x_3135_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8);
v___x_3139_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9);
v___x_3141_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3);
v___x_3142_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3142_, 0, v___x_3141_);
lean_closure_set(v___x_3142_, 1, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3143_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10);
v___x_3144_ = lean_unsigned_to_nat(1024u);
v___x_3145_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3146_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3146_, 0, v___x_3145_);
lean_closure_set(v___x_3146_, 1, v___x_3144_);
lean_closure_set(v___x_3146_, 2, v___x_3143_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer(lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1));
v___x_3153_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11);
v___x_3154_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3152_, v___x_3153_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed(lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_Parser_Term_structInstLVal_parenthesizer(v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7(){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3168_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3169_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3170_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0));
v___x_3171_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3172_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3168_, v___x_3169_, v___x_3170_, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___boxed(lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
return v_res_3174_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__0(void){
_start:
{
uint8_t v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3175_ = 0;
v___x_3176_ = 1;
v___x_3177_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3178_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__0));
v___x_3179_ = l_Lean_Parser_mkAntiquot(v___x_3178_, v___x_3177_, v___x_3176_, v___x_3175_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__1(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3181_ = l_Lean_Parser_fieldIdx;
v___x_3182_ = l_Lean_Parser_orelse(v___x_3181_, v___x_3180_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__2(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__1, &l_Lean_Parser_Term_structInstLVal___closed__1_once, _init_l_Lean_Parser_Term_structInstLVal___closed__1);
v___x_3184_ = l_Lean_Parser_ident;
v___x_3185_ = l_Lean_Parser_orelse(v___x_3184_, v___x_3183_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__3(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__5));
v___x_3187_ = l_Lean_Parser_symbol(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__4(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = l_Lean_Parser_fieldIdx;
v___x_3189_ = l_Lean_Parser_ident;
v___x_3190_ = l_Lean_Parser_orelse(v___x_3189_, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__5(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__4, &l_Lean_Parser_Term_structInstLVal___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal___closed__4);
v___x_3192_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__3, &l_Lean_Parser_Term_structInstLVal___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal___closed__3);
v___x_3193_ = l_Lean_Parser_andthen(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__6(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__5, &l_Lean_Parser_Term_structInstLVal___closed__5_once, _init_l_Lean_Parser_Term_structInstLVal___closed__5);
v___x_3195_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_3196_ = l_Lean_Parser_node(v___x_3195_, v___x_3194_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__7(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3198_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__6, &l_Lean_Parser_Term_structInstLVal___closed__6_once, _init_l_Lean_Parser_Term_structInstLVal___closed__6);
v___x_3199_ = l_Lean_Parser_orelse(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__8(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__7, &l_Lean_Parser_Term_structInstLVal___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal___closed__7);
v___x_3201_ = l_Lean_Parser_many(v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__9(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__8, &l_Lean_Parser_Term_structInstLVal___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal___closed__8);
v___x_3203_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__2, &l_Lean_Parser_Term_structInstLVal___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal___closed__2);
v___x_3204_ = l_Lean_Parser_andthen(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__10(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3205_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__9, &l_Lean_Parser_Term_structInstLVal___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal___closed__9);
v___x_3206_ = lean_unsigned_to_nat(1024u);
v___x_3207_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3208_ = l_Lean_Parser_leadingNode(v___x_3207_, v___x_3206_, v___x_3205_);
return v___x_3208_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__11(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__10, &l_Lean_Parser_Term_structInstLVal___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal___closed__10);
v___x_3210_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__0, &l_Lean_Parser_Term_structInstLVal___closed__0_once, _init_l_Lean_Parser_Term_structInstLVal___closed__0);
v___x_3211_ = l_Lean_Parser_withAntiquot(v___x_3210_, v___x_3209_);
return v___x_3211_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__12(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__11, &l_Lean_Parser_Term_structInstLVal___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal___closed__11);
v___x_3213_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3214_ = l_Lean_Parser_withCache(v___x_3213_, v___x_3212_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal(void){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__12, &l_Lean_Parser_Term_structInstLVal___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal___closed__12);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3));
v___x_3232_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_3233_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3233_, 0, v___x_3232_);
lean_closure_set(v___x_3233_, 1, v___x_3231_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter(lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2));
v___x_3240_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4, &l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4);
v___x_3241_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3239_, v___x_3240_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed(lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_Parser_Term_structInstFieldBinder_formatter(v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
return v_res_3247_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1));
v___x_3258_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_3259_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3259_, 0, v___x_3258_);
lean_closure_set(v___x_3259_, 1, v___x_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0));
v___x_3266_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2);
v___x_3267_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3265_, v___x_3266_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed(lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
return v_res_3273_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0(void){
_start:
{
uint8_t v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3274_ = 1;
v___x_3275_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1));
v___x_3276_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0));
v___x_3277_ = l_Lean_Parser_mkAntiquot(v___x_3276_, v___x_3275_, v___x_3274_, v___x_3274_);
return v___x_3277_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1(void){
_start:
{
uint8_t v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = 0;
v___x_3279_ = l_Lean_Parser_Term_bracketedBinder(v___x_3278_);
return v___x_3279_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__1, &l_Lean_Parser_Term_structInstFieldBinder___closed__1_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1);
v___x_3281_ = l_Lean_Parser_Term_binderIdent;
v___x_3282_ = l_Lean_Parser_orelse(v___x_3281_, v___x_3280_);
return v___x_3282_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__2, &l_Lean_Parser_Term_structInstFieldBinder___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2);
v___x_3284_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__0, &l_Lean_Parser_Term_structInstFieldBinder___closed__0_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0);
v___x_3285_ = l_Lean_Parser_withAntiquot(v___x_3284_, v___x_3283_);
return v___x_3285_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder(void){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__3, &l_Lean_Parser_Term_structInstFieldBinder___closed__3_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3);
return v___x_3286_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0));
v___x_3290_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_3291_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3291_, 0, v___x_3290_);
lean_closure_set(v___x_3291_, 1, v___x_3289_);
return v___x_3291_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1);
v___x_3293_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter(lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2);
v___x_3300_ = l_Lean_Parser_optional_formatter(v___x_3299_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed(lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Parser_Term_optTypeForStructInst_formatter(v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___f_3311_; 
v___x_3309_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0));
v___x_3310_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3311_, 0, v___x_3310_);
lean_closure_set(v___f_3311_, 1, v___x_3309_);
return v___f_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___f_3317_; lean_object* v___x_3318_; 
v___f_3317_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1);
v___x_3318_ = l_Lean_Parser_optional_parenthesizer(v___f_3317_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed(lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
return v_res_3324_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_3326_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_3327_ = l_Lean_Parser_notFollowedBy(v___x_3326_, v___x_3325_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__0, &l_Lean_Parser_Term_optTypeForStructInst___closed__0_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0);
v___x_3329_ = l_Lean_Parser_Term_typeSpec;
v___x_3330_ = l_Lean_Parser_andthen(v___x_3329_, v___x_3328_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__1, &l_Lean_Parser_Term_optTypeForStructInst___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1);
v___x_3332_ = l_Lean_Parser_atomic(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__2, &l_Lean_Parser_Term_optTypeForStructInst___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2);
v___x_3334_ = l_Lean_Parser_optional(v___x_3333_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst(void){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__3, &l_Lean_Parser_Term_optTypeForStructInst___closed__3_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3342_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_3341_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg___boxed(lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter(lean_object* v_rbp_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___boxed(lean_object* v_rbp_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter(v_rbp_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_rbp_3356_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0(lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3364_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0___boxed(lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_Parser_Term_structInstField_formatter___lam__0(v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1(lean_object* v___x_3375_, lean_object* v___x_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3375_, v___x_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed(lean_object* v___x_3383_, lean_object* v___x_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Parser_Term_structInstField_formatter___lam__1(v___x_3383_, v___x_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
return v_res_3390_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__4(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; 
v___x_3405_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed), 5, 0);
v___f_3406_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__0));
v___x_3407_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3407_, 0, v___f_3406_);
lean_closure_set(v___x_3407_, 1, v___x_3405_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__5(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__4, &l_Lean_Parser_Term_structInstField_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__4);
v___x_3409_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_3410_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3410_, 0, v___x_3409_);
lean_closure_set(v___x_3410_, 1, v___x_3408_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__6(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__5, &l_Lean_Parser_Term_structInstField_formatter___closed__5_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__5);
v___x_3412_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__9(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__8));
v___x_3418_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed), 5, 0);
v___x_3419_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3419_, 0, v___x_3418_);
lean_closure_set(v___x_3419_, 1, v___x_3417_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__10(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__9, &l_Lean_Parser_Term_structInstField_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__9);
v___x_3421_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__6, &l_Lean_Parser_Term_structInstField_formatter___closed__6_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__6);
v___x_3422_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3422_, 0, v___x_3421_);
lean_closure_set(v___x_3422_, 1, v___x_3420_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__11(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__10, &l_Lean_Parser_Term_structInstField_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__10);
v___x_3424_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__12(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__11, &l_Lean_Parser_Term_structInstField_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__11);
v___x_3426_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3427_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3427_, 0, v___x_3426_);
lean_closure_set(v___x_3427_, 1, v___x_3425_);
return v___x_3427_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__13(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3428_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__12, &l_Lean_Parser_Term_structInstField_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__12);
v___x_3429_ = lean_unsigned_to_nat(1024u);
v___x_3430_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3431_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3431_, 0, v___x_3430_);
lean_closure_set(v___x_3431_, 1, v___x_3429_);
lean_closure_set(v___x_3431_, 2, v___x_3428_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__14(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___f_3434_; 
v___x_3432_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__13, &l_Lean_Parser_Term_structInstField_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__13);
v___x_3433_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__3));
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed), 7, 2);
lean_closure_set(v___f_3434_, 0, v___x_3433_);
lean_closure_set(v___f_3434_, 1, v___x_3432_);
return v___f_3434_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__15(void){
_start:
{
lean_object* v___f_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___f_3435_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__14, &l_Lean_Parser_Term_structInstField_formatter___closed__14_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__14);
v___x_3436_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3437_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_formatter___boxed), 7, 2);
lean_closure_set(v___x_3437_, 0, v___x_3436_);
lean_closure_set(v___x_3437_, 1, v___f_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter(lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__15, &l_Lean_Parser_Term_structInstField_formatter___closed__15_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__15);
v___x_3444_ = l_Lean_Parser_ppGroup_formatter(v___x_3443_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Parser_Term_structInstField_formatter(v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5(){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3458_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3459_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3460_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0));
v___x_3461_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___boxed), 5, 0);
v___x_3462_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3458_, v___x_3459_, v___x_3460_, v___x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___boxed(lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(lean_object* v_rbp_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3472_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_3471_, v_rbp_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer___boxed(lean_object* v_rbp_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(v_rbp_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
return v_res_3479_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed), 5, 0);
v___x_3489_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__1));
v___x_3490_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3490_, 0, v___x_3489_);
lean_closure_set(v___x_3490_, 1, v___x_3488_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2);
v___x_3492_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_3493_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3493_, 0, v___x_3492_);
lean_closure_set(v___x_3493_, 1, v___x_3491_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3);
v___x_3495_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3495_, 0, v___x_3494_);
return v___x_3495_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__6));
v___x_3501_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed), 5, 0);
v___x_3502_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3502_, 0, v___x_3501_);
lean_closure_set(v___x_3502_, 1, v___x_3500_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__7, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7);
v___x_3504_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__4, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4);
v___x_3505_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3505_, 0, v___x_3504_);
lean_closure_set(v___x_3505_, 1, v___x_3503_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8);
v___x_3507_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3507_, 0, v___x_3506_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9);
v___x_3509_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3510_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3510_, 0, v___x_3509_);
lean_closure_set(v___x_3510_, 1, v___x_3508_);
return v___x_3510_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3511_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10);
v___x_3512_ = lean_unsigned_to_nat(1024u);
v___x_3513_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3514_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3514_, 0, v___x_3513_);
lean_closure_set(v___x_3514_, 1, v___x_3512_);
lean_closure_set(v___x_3514_, 2, v___x_3511_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11);
v___x_3516_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__0));
v___x_3517_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3517_, 0, v___x_3516_);
lean_closure_set(v___x_3517_, 1, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__12, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__12_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12);
v___x_3519_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3520_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3520_, 0, v___x_3519_);
lean_closure_set(v___x_3520_, 1, v___x_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer(lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__13, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__13_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13);
v___x_3527_ = l_Lean_Parser_ppGroup_parenthesizer(v___x_3526_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Parser_Term_structInstField_parenthesizer(v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11(){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3541_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3542_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3543_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0));
v___x_3544_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_parenthesizer___boxed), 5, 0);
v___x_3545_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3541_, v___x_3542_, v___x_3543_, v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___boxed(lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
return v_res_3547_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__0(void){
_start:
{
uint8_t v___x_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3548_ = 0;
v___x_3549_ = 1;
v___x_3550_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3551_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__1));
v___x_3552_ = l_Lean_Parser_mkAntiquot(v___x_3551_, v___x_3550_, v___x_3549_, v___x_3548_);
return v___x_3552_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__2(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Parser_Term_structInstField___closed__1));
v___x_3555_ = l_Lean_Parser_checkColGt(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__3(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = l_Lean_Parser_Term_structInstFieldBinder;
v___x_3557_ = l_Lean_Parser_skip;
v___x_3558_ = l_Lean_Parser_andthen(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__4(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__3, &l_Lean_Parser_Term_structInstField___closed__3_once, _init_l_Lean_Parser_Term_structInstField___closed__3);
v___x_3560_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__2, &l_Lean_Parser_Term_structInstField___closed__2_once, _init_l_Lean_Parser_Term_structInstField___closed__2);
v___x_3561_ = l_Lean_Parser_andthen(v___x_3560_, v___x_3559_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__5(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__4, &l_Lean_Parser_Term_structInstField___closed__4_once, _init_l_Lean_Parser_Term_structInstField___closed__4);
v___x_3563_ = l_Lean_Parser_many(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__6(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_unsigned_to_nat(0u);
v___x_3565_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3566_ = l_Lean_Parser_categoryParser(v___x_3565_, v___x_3564_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__7(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__6, &l_Lean_Parser_Term_structInstField___closed__6_once, _init_l_Lean_Parser_Term_structInstField___closed__6);
v___x_3568_ = l_Lean_Parser_Term_optTypeForStructInst;
v___x_3569_ = l_Lean_Parser_andthen(v___x_3568_, v___x_3567_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__8(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__7, &l_Lean_Parser_Term_structInstField___closed__7_once, _init_l_Lean_Parser_Term_structInstField___closed__7);
v___x_3571_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__5, &l_Lean_Parser_Term_structInstField___closed__5_once, _init_l_Lean_Parser_Term_structInstField___closed__5);
v___x_3572_ = l_Lean_Parser_andthen(v___x_3571_, v___x_3570_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__9(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__8, &l_Lean_Parser_Term_structInstField___closed__8_once, _init_l_Lean_Parser_Term_structInstField___closed__8);
v___x_3574_ = l_Lean_Parser_optional(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__10(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__9, &l_Lean_Parser_Term_structInstField___closed__9_once, _init_l_Lean_Parser_Term_structInstField___closed__9);
v___x_3576_ = l_Lean_Parser_Term_structInstLVal;
v___x_3577_ = l_Lean_Parser_andthen(v___x_3576_, v___x_3575_);
return v___x_3577_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__11(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3578_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__10, &l_Lean_Parser_Term_structInstField___closed__10_once, _init_l_Lean_Parser_Term_structInstField___closed__10);
v___x_3579_ = lean_unsigned_to_nat(1024u);
v___x_3580_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3581_ = l_Lean_Parser_leadingNode(v___x_3580_, v___x_3579_, v___x_3578_);
return v___x_3581_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__12(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__11, &l_Lean_Parser_Term_structInstField___closed__11_once, _init_l_Lean_Parser_Term_structInstField___closed__11);
v___x_3583_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__0, &l_Lean_Parser_Term_structInstField___closed__0_once, _init_l_Lean_Parser_Term_structInstField___closed__0);
v___x_3584_ = l_Lean_Parser_withAntiquot(v___x_3583_, v___x_3582_);
return v___x_3584_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__13(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__12, &l_Lean_Parser_Term_structInstField___closed__12_once, _init_l_Lean_Parser_Term_structInstField___closed__12);
v___x_3586_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3587_ = l_Lean_Parser_withCache(v___x_3586_, v___x_3585_);
return v___x_3587_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField(void){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__13, &l_Lean_Parser_Term_structInstField___closed__13_once, _init_l_Lean_Parser_Term_structInstField___closed__13);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object* v_p_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3602_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_3601_, v_p_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter___boxed(lean_object* v_p_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Parser_Term_structInstFields_formatter(v_p_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object* v_p_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3617_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_3616_, v_p_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer___boxed(lean_object* v_p_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v_p_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields(lean_object* v_p_3625_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3627_ = l_Lean_Parser_node(v___x_3626_, v_p_3625_);
return v___x_3627_;
}
}
lean_object* runtime_initialize_Lean_Parser_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Basic(builtin);
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
