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
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 113, 252, 92, 83, 246, 160, 172)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__3___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_276_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
v___x_277_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_279_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_280_ = l_Lean_Parser_registerAlias(v___x_275_, v___x_276_, v___x_277_, v___x_278_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_281_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_282_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_275_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref_known(v___x_282_, 1);
v___x_283_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_284_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_275_, v___x_283_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref_known(v___x_284_, 1);
v___x_285_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_286_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
v___x_287_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_288_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_289_ = l_Lean_Parser_registerAlias(v___x_285_, v___x_286_, v___x_287_, v___x_288_, v___x_279_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref_known(v___x_289_, 1);
v___x_290_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_291_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_285_, v___x_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref_known(v___x_291_, 1);
v___x_292_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_293_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_285_, v___x_292_);
return v___x_293_;
}
else
{
return v___x_291_;
}
}
else
{
return v___x_289_;
}
}
else
{
return v___x_284_;
}
}
else
{
return v___x_282_;
}
}
else
{
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2____boxed(lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
return v_res_295_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2(void){
_start:
{
uint8_t v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = 0;
v___x_303_ = 1;
v___x_304_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_305_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0));
v___x_306_ = l_Lean_Parser_mkAntiquot(v___x_305_, v___x_304_, v___x_303_, v___x_302_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_309_ = l_Lean_Parser_categoryParser(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_311_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__4);
v___x_313_ = lean_unsigned_to_nat(1024u);
v___x_314_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_315_ = l_Lean_Parser_leadingNode(v___x_314_, v___x_313_, v___x_312_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__5);
v___x_317_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__2);
v___x_318_ = l_Lean_Parser_withAntiquot(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__6);
v___x_320_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_321_ = l_Lean_Parser_withCache(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq1Indented(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__7);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2(void){
_start:
{
uint8_t v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_329_ = 0;
v___x_330_ = 1;
v___x_331_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_332_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0));
v___x_333_ = l_Lean_Parser_mkAntiquot(v___x_332_, v___x_331_, v___x_330_, v___x_329_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__3));
v___x_336_ = l_Lean_Parser_symbol(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_338_ = l_Lean_Parser_Tactic_sepByIndentSemicolon(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_341_ = l_Lean_Parser_symbol(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_343_ = l_Lean_Parser_skip;
v___x_344_ = l_Lean_Parser_andthen(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__8);
v___x_346_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__5);
v___x_347_ = l_Lean_Parser_andthen(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__9);
v___x_349_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__4);
v___x_350_ = l_Lean_Parser_andthen(v___x_349_, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__10);
v___x_352_ = lean_unsigned_to_nat(1024u);
v___x_353_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_354_ = l_Lean_Parser_leadingNode(v___x_353_, v___x_352_, v___x_351_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__11);
v___x_356_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__2);
v___x_357_ = l_Lean_Parser_withAntiquot(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__12);
v___x_359_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_360_ = l_Lean_Parser_withCache(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__13);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1(){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_365_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0));
v___x_366_ = l_Lean_addBuiltinDocString(v___x_364_, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___boxed(lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg(lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_375_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_374_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___redArg___boxed(lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter(lean_object* v_rbp_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Parser_tacticParser_formatter___redArg(v_a_383_, v_a_384_, v_a_385_, v_a_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_formatter___boxed(lean_object* v_rbp_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Parser_tacticParser_formatter(v_rbp_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_rbp_389_);
return v_res_395_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_410_ = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter___boxed), 6, 1);
lean_closure_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_414_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__4);
v___x_415_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_415_, 0, v___x_414_);
lean_closure_set(v___x_415_, 1, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__6);
v___x_417_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__3));
v___x_418_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_418_, 0, v___x_417_);
lean_closure_set(v___x_418_, 1, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__7);
v___x_420_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__1));
v___x_421_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_421_, 0, v___x_420_);
lean_closure_set(v___x_421_, 1, v___x_419_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__8);
v___x_423_ = lean_unsigned_to_nat(1024u);
v___x_424_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_425_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_425_, 0, v___x_424_);
lean_closure_set(v___x_425_, 1, v___x_423_);
lean_closure_set(v___x_425_, 2, v___x_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__0));
v___x_432_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9, &l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__9);
v___x_433_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_431_, v___x_432_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed(lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5(){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_449_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_450_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1));
v___x_451_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_452_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_448_, v___x_449_, v___x_450_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___boxed(lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0));
v___x_474_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2));
v___x_475_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_473_, v___x_474_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed(lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9(){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_489_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_490_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_491_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0));
v___x_492_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_493_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_489_, v___x_490_, v___x_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___boxed(lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
return v_res_495_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_510_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_511_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_511_, 0, v___x_510_);
lean_closure_set(v___x_511_, 1, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_512_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3, &l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__3);
v___x_513_ = lean_unsigned_to_nat(1024u);
v___x_514_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_515_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_515_, 0, v___x_514_);
lean_closure_set(v___x_515_, 1, v___x_513_);
lean_closure_set(v___x_515_, 2, v___x_512_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter(lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_522_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq_formatter___closed__4);
v___x_523_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_521_, v___x_522_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___boxed(lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Parser_Tactic_tacticSeq_formatter(v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13(){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_537_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_538_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_539_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0));
v___x_540_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_541_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_537_, v___x_538_, v___x_539_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___boxed(lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer(lean_object* v_rbp_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_551_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_550_, v_rbp_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tacticParser_parenthesizer___boxed(lean_object* v_rbp_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Parser_tacticParser_parenthesizer(v_rbp_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__0));
v___x_596_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__10));
v___x_597_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_595_, v___x_596_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed(lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19(){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_612_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_613_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_614_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1));
v___x_615_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_616_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_612_, v___x_613_, v___x_614_, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___boxed(lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0));
v___x_638_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2));
v___x_639_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_637_, v___x_638_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed(lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23(){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_653_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_654_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_655_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0));
v___x_656_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_657_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_653_, v___x_654_, v___x_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___boxed(lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
return v_res_659_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_668_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_669_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_669_, 0, v___x_668_);
lean_closure_set(v___x_669_, 1, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1);
v___x_671_ = lean_unsigned_to_nat(1024u);
v___x_672_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_673_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_673_, 0, v___x_672_);
lean_closure_set(v___x_673_, 1, v___x_671_);
lean_closure_set(v___x_673_, 2, v___x_670_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer(lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_680_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2, &l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2);
v___x_681_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_679_, v___x_680_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed(lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Parser_Tactic_tacticSeq_parenthesizer(v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27(){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_696_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_697_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0));
v___x_698_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___x_699_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_695_, v___x_696_, v___x_697_, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___boxed(lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
return v_res_701_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__0(void){
_start:
{
uint8_t v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_702_ = 0;
v___x_703_ = 1;
v___x_704_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_705_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0));
v___x_706_ = l_Lean_Parser_mkAntiquot(v___x_705_, v___x_704_, v___x_703_, v___x_702_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__1(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_708_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_709_ = l_Lean_Parser_orelse(v___x_708_, v___x_707_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__2(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__1, &l_Lean_Parser_Tactic_tacticSeq___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__1);
v___x_711_ = lean_unsigned_to_nat(1024u);
v___x_712_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_713_ = l_Lean_Parser_leadingNode(v___x_712_, v___x_711_, v___x_710_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__2, &l_Lean_Parser_Tactic_tacticSeq___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__2);
v___x_715_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_716_ = l_Lean_Parser_withAntiquot(v___x_715_, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq___closed__4(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__3, &l_Lean_Parser_Tactic_tacticSeq___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__3);
v___x_718_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_719_ = l_Lean_Parser_withCache(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeq(void){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__4, &l_Lean_Parser_Tactic_tacticSeq___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__4);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1(){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_724_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0));
v___x_725_ = l_Lean_addBuiltinDocString(v___x_723_, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___boxed(lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
return v_res_727_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_730_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_731_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_731_, 0, v___x_730_);
lean_closure_set(v___x_731_, 1, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2));
v___x_736_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1);
v___x_737_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_737_, 0, v___x_736_);
lean_closure_set(v___x_737_, 1, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__3);
v___x_739_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_740_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_740_, 0, v___x_739_);
lean_closure_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__4);
v___x_742_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_743_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_743_, 0, v___x_742_);
lean_closure_set(v___x_743_, 1, v___x_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_750_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__5);
v___x_751_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_749_, v___x_750_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3(){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_766_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_767_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_768_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1));
v___x_769_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed), 5, 0);
v___x_770_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_766_, v___x_767_, v___x_768_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___boxed(lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
return v_res_772_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_775_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_776_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_776_, 0, v___x_775_);
lean_closure_set(v___x_776_, 1, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2));
v___x_781_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1);
v___x_782_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_782_, 0, v___x_781_);
lean_closure_set(v___x_782_, 1, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__3);
v___x_784_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_785_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_785_, 0, v___x_784_);
lean_closure_set(v___x_785_, 1, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__4);
v___x_787_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_788_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_788_, 0, v___x_787_);
lean_closure_set(v___x_788_, 1, v___x_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_795_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__5);
v___x_796_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_794_, v___x_795_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7(){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_810_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_811_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_812_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0));
v___x_813_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed), 5, 0);
v___x_814_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_810_, v___x_811_, v___x_812_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___boxed(lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
return v_res_816_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0));
v___x_819_ = l_Lean_Parser_checkColGt(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_821_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1);
v___x_822_ = l_Lean_Parser_andthen(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_Parser_pushNone;
v___x_824_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_825_ = l_Lean_Parser_node(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3);
v___x_827_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2);
v___x_828_ = l_Lean_Parser_orelse(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4);
v___x_830_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_831_ = l_Lean_Parser_orelse(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5);
v___x_833_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_834_ = l_Lean_Parser_node(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__6);
v___x_836_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_837_ = l_Lean_Parser_withAntiquot(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt(void){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__7);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1(){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0));
v___x_847_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1));
v___x_848_ = l_Lean_addBuiltinDocString(v___x_846_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___boxed(lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter(lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_872_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__4));
v___x_873_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_871_, v___x_872_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter___boxed(lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Parser_Tactic_seq1_formatter(v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3(){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_888_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_889_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0));
v___x_890_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_formatter___boxed), 5, 0);
v___x_891_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_887_, v___x_888_, v___x_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer(lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_908_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1));
v___x_909_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_907_, v___x_908_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___boxed(lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Parser_Tactic_seq1_parenthesizer(v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7(){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_923_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_924_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_925_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0));
v___x_926_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_parenthesizer___boxed), 5, 0);
v___x_927_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_923_, v___x_924_, v___x_925_, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___boxed(lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
return v_res_929_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__0(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_931_ = l_Lean_Parser_symbol(v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__1(void){
_start:
{
uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_932_ = 1;
v___x_933_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__0, &l_Lean_Parser_Tactic_seq1___closed__0_once, _init_l_Lean_Parser_Tactic_seq1___closed__0);
v___x_934_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_935_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_936_ = l_Lean_Parser_sepBy1(v___x_935_, v___x_934_, v___x_933_, v___x_932_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__1, &l_Lean_Parser_Tactic_seq1___closed__1_once, _init_l_Lean_Parser_Tactic_seq1___closed__1);
v___x_938_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_939_ = l_Lean_Parser_node(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1(void){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__2, &l_Lean_Parser_Tactic_seq1___closed__2_once, _init_l_Lean_Parser_Tactic_seq1___closed__2);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__2(void){
_start:
{
uint8_t v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_947_ = 0;
v___x_948_ = 1;
v___x_949_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_950_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__0));
v___x_951_ = l_Lean_Parser_mkAntiquot(v___x_950_, v___x_949_, v___x_948_, v___x_947_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__4(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__3));
v___x_954_ = l_Lean_Parser_symbol(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__5(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_956_ = lean_unsigned_to_nat(1024u);
v___x_957_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_958_ = l_Lean_Parser_leadingNode(v___x_957_, v___x_956_, v___x_955_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__6(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__5, &l_Lean_Parser_Term_hole___closed__5_once, _init_l_Lean_Parser_Term_hole___closed__5);
v___x_960_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__2, &l_Lean_Parser_Term_hole___closed__2_once, _init_l_Lean_Parser_Term_hole___closed__2);
v___x_961_ = l_Lean_Parser_withAntiquot(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__7(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__6, &l_Lean_Parser_Term_hole___closed__6_once, _init_l_Lean_Parser_Term_hole___closed__6);
v___x_963_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_964_ = l_Lean_Parser_withCache(v___x_963_, v___x_962_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole(void){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__7, &l_Lean_Parser_Term_hole___closed__7_once, _init_l_Lean_Parser_Term_hole___closed__7);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1(){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_970_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_971_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_972_ = l_Lean_Parser_Term_hole;
v___x_973_ = lean_unsigned_to_nat(1000u);
v___x_974_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_970_, v___x_971_, v___x_972_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___boxed(lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3(){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_980_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0));
v___x_981_ = l_Lean_addBuiltinDocString(v___x_979_, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___boxed(lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5(){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1011_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6));
v___x_1012_ = l_Lean_addBuiltinDeclarationRanges(v___x_1010_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___boxed(lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter(lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__0));
v___x_1034_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__2));
v___x_1035_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1033_, v___x_1034_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Parser_Term_hole_formatter(v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9(){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1049_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1050_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1051_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0));
v___x_1052_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1053_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1049_, v___x_1050_, v___x_1051_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___boxed(lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer(lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__0));
v___x_1075_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__2));
v___x_1076_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1074_, v___x_1075_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Parser_Term_hole_parenthesizer(v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13(){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1090_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1091_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0));
v___x_1093_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1094_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1090_, v___x_1091_, v___x_1092_, v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___boxed(lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__2(void){
_start:
{
uint8_t v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1103_ = 0;
v___x_1104_ = 1;
v___x_1105_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1106_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__0));
v___x_1107_ = l_Lean_Parser_mkAntiquot(v___x_1106_, v___x_1105_, v___x_1104_, v___x_1103_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__4(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__3));
v___x_1110_ = l_Lean_Parser_symbol(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__5(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_1112_ = l_Lean_Parser_ident;
v___x_1113_ = l_Lean_Parser_orelse(v___x_1112_, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__6(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__5, &l_Lean_Parser_Term_syntheticHole___closed__5_once, _init_l_Lean_Parser_Term_syntheticHole___closed__5);
v___x_1115_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__4, &l_Lean_Parser_Term_syntheticHole___closed__4_once, _init_l_Lean_Parser_Term_syntheticHole___closed__4);
v___x_1116_ = l_Lean_Parser_andthen(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__7(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__6, &l_Lean_Parser_Term_syntheticHole___closed__6_once, _init_l_Lean_Parser_Term_syntheticHole___closed__6);
v___x_1118_ = lean_unsigned_to_nat(1024u);
v___x_1119_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1120_ = l_Lean_Parser_leadingNode(v___x_1119_, v___x_1118_, v___x_1117_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__8(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__7, &l_Lean_Parser_Term_syntheticHole___closed__7_once, _init_l_Lean_Parser_Term_syntheticHole___closed__7);
v___x_1122_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__2, &l_Lean_Parser_Term_syntheticHole___closed__2_once, _init_l_Lean_Parser_Term_syntheticHole___closed__2);
v___x_1123_ = l_Lean_Parser_withAntiquot(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__9(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__8, &l_Lean_Parser_Term_syntheticHole___closed__8_once, _init_l_Lean_Parser_Term_syntheticHole___closed__8);
v___x_1125_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1126_ = l_Lean_Parser_withCache(v___x_1125_, v___x_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole(void){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__9, &l_Lean_Parser_Term_syntheticHole___closed__9_once, _init_l_Lean_Parser_Term_syntheticHole___closed__9);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1(){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1130_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1131_ = l_Lean_Parser_Term_syntheticHole;
v___x_1132_ = lean_unsigned_to_nat(1000u);
v___x_1133_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1129_, v___x_1130_, v___x_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1___boxed(lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3(){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1139_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0));
v___x_1140_ = l_Lean_addBuiltinDocString(v___x_1138_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___boxed(lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5(){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1170_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6));
v___x_1171_ = l_Lean_addBuiltinDeclarationRanges(v___x_1169_, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___boxed(lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter(lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__0));
v___x_1200_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__5));
v___x_1201_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1199_, v___x_1200_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter___boxed(lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Parser_Term_syntheticHole_formatter(v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9(){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1215_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1216_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1217_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0));
v___x_1218_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_formatter___boxed), 5, 0);
v___x_1219_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1215_, v___x_1216_, v___x_1217_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___boxed(lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer(lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0));
v___x_1248_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5));
v___x_1249_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1247_, v___x_1248_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed(lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Parser_Term_syntheticHole_parenthesizer(v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13(){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1263_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1264_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1265_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0));
v___x_1266_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed), 5, 0);
v___x_1267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1263_, v___x_1264_, v___x_1265_, v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___boxed(lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
return v_res_1269_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__2(void){
_start:
{
uint8_t v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1276_ = 0;
v___x_1277_ = 1;
v___x_1278_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1279_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__0));
v___x_1280_ = l_Lean_Parser_mkAntiquot(v___x_1279_, v___x_1278_, v___x_1277_, v___x_1276_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__4(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__3));
v___x_1283_ = l_Lean_Parser_symbol(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__5(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__4, &l_Lean_Parser_Term_omission___closed__4_once, _init_l_Lean_Parser_Term_omission___closed__4);
v___x_1285_ = lean_unsigned_to_nat(1024u);
v___x_1286_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1287_ = l_Lean_Parser_leadingNode(v___x_1286_, v___x_1285_, v___x_1284_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__6(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__5, &l_Lean_Parser_Term_omission___closed__5_once, _init_l_Lean_Parser_Term_omission___closed__5);
v___x_1289_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__2, &l_Lean_Parser_Term_omission___closed__2_once, _init_l_Lean_Parser_Term_omission___closed__2);
v___x_1290_ = l_Lean_Parser_withAntiquot(v___x_1289_, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__7(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__6, &l_Lean_Parser_Term_omission___closed__6_once, _init_l_Lean_Parser_Term_omission___closed__6);
v___x_1292_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1293_ = l_Lean_Parser_withCache(v___x_1292_, v___x_1291_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission(void){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__7, &l_Lean_Parser_Term_omission___closed__7_once, _init_l_Lean_Parser_Term_omission___closed__7);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1(){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1297_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1298_ = l_Lean_Parser_Term_omission;
v___x_1299_ = lean_unsigned_to_nat(1000u);
v___x_1300_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1296_, v___x_1297_, v___x_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1___boxed(lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3(){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1306_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0));
v___x_1307_ = l_Lean_addBuiltinDocString(v___x_1305_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___boxed(lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5(){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1337_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6));
v___x_1338_ = l_Lean_addBuiltinDeclarationRanges(v___x_1336_, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___boxed(lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter(lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__0));
v___x_1360_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__2));
v___x_1361_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1359_, v___x_1360_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter___boxed(lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Parser_Term_omission_formatter(v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9(){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1375_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1376_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1377_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0));
v___x_1378_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_formatter___boxed), 5, 0);
v___x_1379_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1375_, v___x_1376_, v___x_1377_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___boxed(lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer(lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__0));
v___x_1401_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__2));
v___x_1402_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1400_, v___x_1401_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer___boxed(lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Parser_Term_omission_parenthesizer(v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13(){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1416_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1417_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1418_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0));
v___x_1419_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_parenthesizer___boxed), 5, 0);
v___x_1420_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1416_, v___x_1417_, v___x_1418_, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___boxed(lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_1429_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1430_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1428_, v___x_1429_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter___boxed(lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Parser_Term_binderIdent_formatter(v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_1443_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1444_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_1442_, v___x_1443_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer___boxed(lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Parser_Term_binderIdent_parenthesizer(v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
return v_res_1450_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent___closed__0(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = l_Lean_Parser_Term_hole;
v___x_1452_ = l_Lean_Parser_ident;
v___x_1453_ = l_Lean_Parser_orelse(v___x_1452_, v___x_1451_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent(void){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_obj_once(&l_Lean_Parser_Term_binderIdent___closed__0, &l_Lean_Parser_Term_binderIdent___closed__0_once, _init_l_Lean_Parser_Term_binderIdent___closed__0);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter(uint8_t v_requireType_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (v_requireType_1466_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1473_ = l_Lean_Parser_optional_formatter(v___x_1472_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1475_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1476_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1474_, v___x_1475_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter___boxed(lean_object* v_requireType_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
uint8_t v_requireType_boxed_1483_; lean_object* v_res_1484_; 
v_requireType_boxed_1483_ = lean_unbox(v_requireType_1477_);
v_res_1484_ = l_Lean_Parser_Term_binderType_formatter(v_requireType_boxed_1483_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer(uint8_t v_requireType_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
if (v_requireType_1492_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1499_ = l_Lean_Parser_optional_parenthesizer(v___x_1498_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1501_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1502_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1500_, v___x_1501_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer___boxed(lean_object* v_requireType_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
uint8_t v_requireType_boxed_1509_; lean_object* v_res_1510_; 
v_requireType_boxed_1509_ = lean_unbox(v_requireType_1503_);
v_res_1510_ = l_Lean_Parser_Term_binderType_parenthesizer(v_requireType_boxed_1509_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1510_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__0(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__0));
v___x_1512_ = l_Lean_Parser_symbol(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = l_Lean_Parser_termParser(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__2(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1516_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1517_ = l_Lean_Parser_andthen(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__3(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1519_ = l_Lean_Parser_optional(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__4(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1521_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1522_ = l_Lean_Parser_node(v___x_1521_, v___x_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType(uint8_t v_requireType_1523_){
_start:
{
if (v_requireType_1523_ == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__3, &l_Lean_Parser_Term_binderType___closed__3_once, _init_l_Lean_Parser_Term_binderType___closed__3);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__4, &l_Lean_Parser_Term_binderType___closed__4_once, _init_l_Lean_Parser_Term_binderType___closed__4);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType___boxed(lean_object* v_requireType_1526_){
_start:
{
uint8_t v_requireType_boxed_1527_; lean_object* v_res_1528_; 
v_requireType_boxed_1527_ = lean_unbox(v_requireType_1526_);
v_res_1528_ = l_Lean_Parser_Term_binderType(v_requireType_boxed_1527_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_1554_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__8));
v___x_1555_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1555_, 0, v___x_1554_);
lean_closure_set(v___x_1555_, 1, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1556_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__9, &l_Lean_Parser_Term_binderTactic_formatter___closed__9_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9);
v___x_1557_ = lean_unsigned_to_nat(1024u);
v___x_1558_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1559_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1559_, 0, v___x_1558_);
lean_closure_set(v___x_1559_, 1, v___x_1557_);
lean_closure_set(v___x_1559_, 2, v___x_1556_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter(lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__2));
v___x_1566_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__10, &l_Lean_Parser_Term_binderTactic_formatter___closed__10_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10);
v___x_1567_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1565_, v___x_1566_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter___boxed(lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Parser_Term_binderTactic_formatter(v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3(){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1581_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1582_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1583_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0));
v___x_1584_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_1585_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1581_, v___x_1582_, v___x_1583_, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___boxed(lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_1588_, v___x_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed(lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(v___x_1596_, v___x_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1603_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___f_1619_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3));
v___x_1620_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1620_, 0, v___f_1619_);
lean_closure_set(v___x_1620_, 1, v___x_1618_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4);
v___x_1622_ = lean_unsigned_to_nat(1024u);
v___x_1623_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1624_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1624_, 0, v___x_1623_);
lean_closure_set(v___x_1624_, 1, v___x_1622_);
lean_closure_set(v___x_1624_, 2, v___x_1621_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer(lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0));
v___x_1631_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5);
v___x_1632_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1630_, v___x_1631_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___boxed(lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Parser_Term_binderTactic_parenthesizer(v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7(){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1646_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1647_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1648_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0));
v___x_1649_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_1650_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1646_, v___x_1647_, v___x_1648_, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___boxed(lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
return v_res_1652_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__0(void){
_start:
{
uint8_t v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1653_ = 0;
v___x_1654_ = 1;
v___x_1655_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1656_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__0));
v___x_1657_ = l_Lean_Parser_mkAntiquot(v___x_1656_, v___x_1655_, v___x_1654_, v___x_1653_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__1(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__3));
v___x_1659_ = l_Lean_Parser_symbol(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__2(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__5));
v___x_1661_ = l_Lean_Parser_symbol(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__3(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__2, &l_Lean_Parser_Term_binderTactic___closed__2_once, _init_l_Lean_Parser_Term_binderTactic___closed__2);
v___x_1663_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1664_ = l_Lean_Parser_andthen(v___x_1663_, v___x_1662_);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__4(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__3, &l_Lean_Parser_Term_binderTactic___closed__3_once, _init_l_Lean_Parser_Term_binderTactic___closed__3);
v___x_1666_ = l_Lean_Parser_atomic(v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__5(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_1668_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__4, &l_Lean_Parser_Term_binderTactic___closed__4_once, _init_l_Lean_Parser_Term_binderTactic___closed__4);
v___x_1669_ = l_Lean_Parser_andthen(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__6(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1670_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__5, &l_Lean_Parser_Term_binderTactic___closed__5_once, _init_l_Lean_Parser_Term_binderTactic___closed__5);
v___x_1671_ = lean_unsigned_to_nat(1024u);
v___x_1672_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1673_ = l_Lean_Parser_leadingNode(v___x_1672_, v___x_1671_, v___x_1670_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__7(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__6, &l_Lean_Parser_Term_binderTactic___closed__6_once, _init_l_Lean_Parser_Term_binderTactic___closed__6);
v___x_1675_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__0, &l_Lean_Parser_Term_binderTactic___closed__0_once, _init_l_Lean_Parser_Term_binderTactic___closed__0);
v___x_1676_ = l_Lean_Parser_withAntiquot(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__8(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__7, &l_Lean_Parser_Term_binderTactic___closed__7_once, _init_l_Lean_Parser_Term_binderTactic___closed__7);
v___x_1678_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1679_ = l_Lean_Parser_withCache(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic(void){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__8, &l_Lean_Parser_Term_binderTactic___closed__8_once, _init_l_Lean_Parser_Term_binderTactic___closed__8);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__2(void){
_start:
{
uint8_t v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1687_ = 0;
v___x_1688_ = 1;
v___x_1689_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1690_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__0));
v___x_1691_ = l_Lean_Parser_mkAntiquot(v___x_1690_, v___x_1689_, v___x_1688_, v___x_1687_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__3(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1693_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1694_ = l_Lean_Parser_andthen(v___x_1693_, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__4(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1695_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__3, &l_Lean_Parser_Term_binderDefault___closed__3_once, _init_l_Lean_Parser_Term_binderDefault___closed__3);
v___x_1696_ = lean_unsigned_to_nat(1024u);
v___x_1697_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1698_ = l_Lean_Parser_leadingNode(v___x_1697_, v___x_1696_, v___x_1695_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__5(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__4, &l_Lean_Parser_Term_binderDefault___closed__4_once, _init_l_Lean_Parser_Term_binderDefault___closed__4);
v___x_1700_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__2, &l_Lean_Parser_Term_binderDefault___closed__2_once, _init_l_Lean_Parser_Term_binderDefault___closed__2);
v___x_1701_ = l_Lean_Parser_withAntiquot(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__6(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__5, &l_Lean_Parser_Term_binderDefault___closed__5_once, _init_l_Lean_Parser_Term_binderDefault___closed__5);
v___x_1703_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1704_ = l_Lean_Parser_withCache(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault(void){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__6, &l_Lean_Parser_Term_binderDefault___closed__6_once, _init_l_Lean_Parser_Term_binderDefault___closed__6);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM(void){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Parser_Term_binderDefault;
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v_stxTrav_1710_; lean_object* v_cur_1711_; lean_object* v___x_1712_; 
v___x_1709_ = lean_st_ref_get(v___y_1707_);
v_stxTrav_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_stxTrav_1710_);
lean_dec(v___x_1709_);
v_cur_1711_ = lean_ctor_get(v_stxTrav_1710_, 0);
lean_inc(v_cur_1711_);
lean_dec_ref(v_stxTrav_1710_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_cur_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1713_);
lean_dec(v___y_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1717_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___boxed(lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1735_; 
lean_dec_ref_known(v___x_1734_, 1);
v___x_1735_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_1730_);
return v___x_1735_;
}
else
{
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed(lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer(lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v_a_1755_; lean_object* v___y_1757_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1754_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v_a_1750_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_n(v_a_1755_, 2);
lean_dec_ref(v___x_1754_);
v___x_1760_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1761_ = l_Lean_Syntax_isOfKind(v_a_1755_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_dec(v_a_1755_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___y_1757_ = v___x_1762_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = l_Lean_Syntax_getArg(v_a_1755_, v___x_1763_);
lean_dec(v_a_1755_);
v___x_1765_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1));
v___x_1766_ = l_Lean_Syntax_isOfKind(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___y_1757_ = v___x_1767_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Parser_maxPrec;
v___y_1757_ = v___x_1768_;
goto v___jp_1756_;
}
}
v___jp_1756_:
{
lean_object* v___f_1758_; lean_object* v___x_1759_; 
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1758_, 0, v___y_1757_);
v___x_1759_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___f_1758_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___boxed(lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Parser_Term_binderDefault_parenthesizer(v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1774_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = 0;
v___x_1782_ = 1;
v___x_1783_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1784_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__0));
v___x_1785_ = l_Lean_Parser_mkAntiquot(v___x_1784_, v___x_1783_, v___x_1782_, v___x_1781_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__3));
v___x_1788_ = l_Lean_Parser_symbol(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__5(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = l_Lean_Parser_Term_binderIdent;
v___x_1790_ = l_Lean_Parser_many1(v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__6(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = l_Lean_Parser_Term_binderDefault;
v___x_1792_ = l_Lean_Parser_Term_binderTactic;
v___x_1793_ = l_Lean_Parser_orelse(v___x_1792_, v___x_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__7(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__6, &l_Lean_Parser_Term_explicitBinder___closed__6_once, _init_l_Lean_Parser_Term_explicitBinder___closed__6);
v___x_1795_ = l_Lean_Parser_optional(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__9(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__8));
v___x_1798_ = l_Lean_Parser_symbol(v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder(uint8_t v_requireType_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1800_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1801_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__2, &l_Lean_Parser_Term_explicitBinder___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder___closed__2);
v___x_1802_ = lean_unsigned_to_nat(1024u);
v___x_1803_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__4, &l_Lean_Parser_Term_explicitBinder___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder___closed__4);
v___x_1804_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1805_ = l_Lean_Parser_Term_binderType(v_requireType_1799_);
v___x_1806_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__7, &l_Lean_Parser_Term_explicitBinder___closed__7_once, _init_l_Lean_Parser_Term_explicitBinder___closed__7);
v___x_1807_ = l_Lean_Parser_andthen(v___x_1805_, v___x_1806_);
v___x_1808_ = l_Lean_Parser_andthen(v___x_1804_, v___x_1807_);
v___x_1809_ = l_Lean_Parser_withoutPosition(v___x_1808_);
v___x_1810_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__9, &l_Lean_Parser_Term_explicitBinder___closed__9_once, _init_l_Lean_Parser_Term_explicitBinder___closed__9);
v___x_1811_ = l_Lean_Parser_andthen(v___x_1809_, v___x_1810_);
v___x_1812_ = l_Lean_Parser_andthen(v___x_1803_, v___x_1811_);
v___x_1813_ = l_Lean_Parser_leadingNode(v___x_1800_, v___x_1802_, v___x_1812_);
v___x_1814_ = l_Lean_Parser_withAntiquot(v___x_1801_, v___x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___boxed(lean_object* v_requireType_1815_){
_start:
{
uint8_t v_requireType_boxed_1816_; lean_object* v_res_1817_; 
v_requireType_boxed_1816_ = lean_unbox(v_requireType_1815_);
v_res_1817_ = l_Lean_Parser_Term_explicitBinder(v_requireType_boxed_1816_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1(){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1821_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0));
v___x_1822_ = l_Lean_addBuiltinDocString(v___x_1820_, v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___boxed(lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
return v_res_1824_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1831_ = 0;
v___x_1832_ = 1;
v___x_1833_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1834_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__0));
v___x_1835_ = l_Lean_Parser_mkAntiquot(v___x_1834_, v___x_1833_, v___x_1832_, v___x_1831_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__3));
v___x_1838_ = l_Lean_Parser_symbol(v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder(uint8_t v_requireType_1839_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1840_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1841_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__2, &l_Lean_Parser_Term_implicitBinder___closed__2_once, _init_l_Lean_Parser_Term_implicitBinder___closed__2);
v___x_1842_ = lean_unsigned_to_nat(1024u);
v___x_1843_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1844_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1845_ = l_Lean_Parser_Term_binderType(v_requireType_1839_);
v___x_1846_ = l_Lean_Parser_andthen(v___x_1844_, v___x_1845_);
v___x_1847_ = l_Lean_Parser_withoutPosition(v___x_1846_);
v___x_1848_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1849_ = l_Lean_Parser_andthen(v___x_1847_, v___x_1848_);
v___x_1850_ = l_Lean_Parser_andthen(v___x_1843_, v___x_1849_);
v___x_1851_ = l_Lean_Parser_leadingNode(v___x_1840_, v___x_1842_, v___x_1850_);
v___x_1852_ = l_Lean_Parser_withAntiquot(v___x_1841_, v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___boxed(lean_object* v_requireType_1853_){
_start:
{
uint8_t v_requireType_boxed_1854_; lean_object* v_res_1855_; 
v_requireType_boxed_1854_ = lean_unbox(v_requireType_1853_);
v_res_1855_ = l_Lean_Parser_Term_implicitBinder(v_requireType_boxed_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1(){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1859_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0));
v___x_1860_ = l_Lean_addBuiltinDocString(v___x_1858_, v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___boxed(lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
return v_res_1862_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1864_ = l_Lean_Parser_andthen(v___x_1863_, v___x_1863_);
return v___x_1864_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0);
v___x_1869_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1870_ = l_Lean_Parser_node(v___x_1869_, v___x_1868_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3);
v___x_1872_ = l_Lean_Parser_atomic(v___x_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5));
v___x_1875_ = l_Lean_Parser_symbol(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6);
v___x_1877_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4);
v___x_1878_ = l_Lean_Parser_orelse(v___x_1877_, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket(void){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1881_ = l_Lean_Parser_andthen(v___x_1880_, v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__0, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0);
v___x_1883_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1884_ = l_Lean_Parser_node(v___x_1883_, v___x_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__1, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1);
v___x_1886_ = l_Lean_Parser_atomic(v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket___closed__3));
v___x_1889_ = l_Lean_Parser_symbol(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__4, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4);
v___x_1891_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__2, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2);
v___x_1892_ = l_Lean_Parser_orelse(v___x_1891_, v___x_1890_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket(void){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__5, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__5_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5);
return v___x_1893_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1900_ = 0;
v___x_1901_ = 1;
v___x_1902_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1903_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__0));
v___x_1904_ = l_Lean_Parser_mkAntiquot(v___x_1903_, v___x_1902_, v___x_1901_, v___x_1900_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder(uint8_t v_requireType_1905_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1906_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1907_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitBinder___closed__2, &l_Lean_Parser_Term_strictImplicitBinder___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2);
v___x_1908_ = lean_unsigned_to_nat(1024u);
v___x_1909_ = l_Lean_Parser_Term_strictImplicitLeftBracket;
v___x_1910_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1911_ = l_Lean_Parser_Term_binderType(v_requireType_1905_);
v___x_1912_ = l_Lean_Parser_Term_strictImplicitRightBracket;
v___x_1913_ = l_Lean_Parser_andthen(v___x_1911_, v___x_1912_);
v___x_1914_ = l_Lean_Parser_andthen(v___x_1910_, v___x_1913_);
v___x_1915_ = l_Lean_Parser_andthen(v___x_1909_, v___x_1914_);
v___x_1916_ = l_Lean_Parser_leadingNode(v___x_1906_, v___x_1908_, v___x_1915_);
v___x_1917_ = l_Lean_Parser_withAntiquot(v___x_1907_, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___boxed(lean_object* v_requireType_1918_){
_start:
{
uint8_t v_requireType_boxed_1919_; lean_object* v_res_1920_; 
v_requireType_boxed_1919_ = lean_unbox(v_requireType_1918_);
v_res_1920_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_boxed_1919_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1(){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1924_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0));
v___x_1925_ = l_Lean_addBuiltinDocString(v___x_1923_, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
return v_res_1927_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__0(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1929_ = l_Lean_Parser_ident;
v___x_1930_ = l_Lean_Parser_andthen(v___x_1929_, v___x_1928_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__1(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__0, &l_Lean_Parser_Term_optIdent___closed__0_once, _init_l_Lean_Parser_Term_optIdent___closed__0);
v___x_1932_ = l_Lean_Parser_atomic(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__2(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__1, &l_Lean_Parser_Term_optIdent___closed__1_once, _init_l_Lean_Parser_Term_optIdent___closed__1);
v___x_1934_ = l_Lean_Parser_optional(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent(void){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__2, &l_Lean_Parser_Term_optIdent___closed__2_once, _init_l_Lean_Parser_Term_optIdent___closed__2);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__2(void){
_start:
{
uint8_t v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1942_ = 0;
v___x_1943_ = 1;
v___x_1944_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1945_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__0));
v___x_1946_ = l_Lean_Parser_mkAntiquot(v___x_1945_, v___x_1944_, v___x_1943_, v___x_1942_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__4(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__3));
v___x_1949_ = l_Lean_Parser_symbol(v___x_1948_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__5(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1951_ = l_Lean_Parser_Term_optIdent;
v___x_1952_ = l_Lean_Parser_andthen(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__6(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__5, &l_Lean_Parser_Term_instBinder___closed__5_once, _init_l_Lean_Parser_Term_instBinder___closed__5);
v___x_1954_ = l_Lean_Parser_withoutPosition(v___x_1953_);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__8(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__7));
v___x_1957_ = l_Lean_Parser_symbol(v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__9(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_1959_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__6, &l_Lean_Parser_Term_instBinder___closed__6_once, _init_l_Lean_Parser_Term_instBinder___closed__6);
v___x_1960_ = l_Lean_Parser_andthen(v___x_1959_, v___x_1958_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__10(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__9, &l_Lean_Parser_Term_instBinder___closed__9_once, _init_l_Lean_Parser_Term_instBinder___closed__9);
v___x_1962_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_1963_ = l_Lean_Parser_andthen(v___x_1962_, v___x_1961_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__11(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1964_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__10, &l_Lean_Parser_Term_instBinder___closed__10_once, _init_l_Lean_Parser_Term_instBinder___closed__10);
v___x_1965_ = lean_unsigned_to_nat(1024u);
v___x_1966_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1967_ = l_Lean_Parser_leadingNode(v___x_1966_, v___x_1965_, v___x_1964_);
return v___x_1967_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__12(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__11, &l_Lean_Parser_Term_instBinder___closed__11_once, _init_l_Lean_Parser_Term_instBinder___closed__11);
v___x_1969_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__2, &l_Lean_Parser_Term_instBinder___closed__2_once, _init_l_Lean_Parser_Term_instBinder___closed__2);
v___x_1970_ = l_Lean_Parser_withAntiquot(v___x_1969_, v___x_1968_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__13(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__12, &l_Lean_Parser_Term_instBinder___closed__12_once, _init_l_Lean_Parser_Term_instBinder___closed__12);
v___x_1972_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1973_ = l_Lean_Parser_withCache(v___x_1972_, v___x_1971_);
return v___x_1973_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder(void){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__13, &l_Lean_Parser_Term_instBinder___closed__13_once, _init_l_Lean_Parser_Term_instBinder___closed__13);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1(){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1978_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0));
v___x_1979_ = l_Lean_addBuiltinDocString(v___x_1977_, v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___boxed(lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter(lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__0));
v___x_2002_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__2));
v___x_2003_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2001_, v___x_2002_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter___boxed(lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Parser_Term_binderDefault_formatter(v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3(){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2017_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2018_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_2019_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0));
v___x_2020_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2021_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2017_, v___x_2018_, v___x_2019_, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___boxed(lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
return v_res_2023_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_2034_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter___boxed), 6, 1);
lean_closure_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_2037_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2037_, 0, v___x_2036_);
lean_closure_set(v___x_2037_, 1, v___x_2035_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__3, &l_Lean_Parser_Term_explicitBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3);
v___x_2039_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter(uint8_t v_requireType_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2048_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2049_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__0));
v___x_2050_ = lean_unsigned_to_nat(1024u);
v___x_2051_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__1));
v___x_2052_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2053_ = lean_box(v_requireType_2042_);
v___x_2054_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2054_, 0, v___x_2053_);
v___x_2055_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__4, &l_Lean_Parser_Term_explicitBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4);
v___x_2056_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2056_, 0, v___x_2054_);
lean_closure_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2057_, 0, v___x_2052_);
lean_closure_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2058_, 0, v___x_2057_);
v___x_2059_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__5));
v___x_2060_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2060_, 0, v___x_2058_);
lean_closure_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2061_, 0, v___x_2051_);
lean_closure_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2062_, 0, v___x_2061_);
v___x_2063_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2063_, 0, v___x_2048_);
lean_closure_set(v___x_2063_, 1, v___x_2050_);
lean_closure_set(v___x_2063_, 2, v___x_2062_);
v___x_2064_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2049_, v___x_2063_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter___boxed(lean_object* v_requireType_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
uint8_t v_requireType_boxed_2071_; lean_object* v_res_2072_; 
v_requireType_boxed_2071_ = lean_unbox(v_requireType_2065_);
v_res_2072_ = l_Lean_Parser_Term_explicitBinder_formatter(v_requireType_boxed_2071_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3));
v___x_2089_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4));
v___x_2090_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2088_, v___x_2089_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed(lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter(lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2));
v___x_2111_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3));
v___x_2112_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2110_, v___x_2111_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed(lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Parser_Term_strictImplicitRightBracket_formatter(v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter(uint8_t v_requireType_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2132_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2133_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0));
v___x_2134_ = lean_unsigned_to_nat(1024u);
v___x_2135_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed), 5, 0);
v___x_2136_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2137_ = lean_box(v_requireType_2126_);
v___x_2138_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2138_, 0, v___x_2137_);
v___x_2139_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed), 5, 0);
v___x_2140_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2140_, 0, v___x_2138_);
lean_closure_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2141_, 0, v___x_2136_);
lean_closure_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2142_, 0, v___x_2135_);
lean_closure_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2143_, 0, v___x_2142_);
v___x_2144_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2144_, 0, v___x_2132_);
lean_closure_set(v___x_2144_, 1, v___x_2134_);
lean_closure_set(v___x_2144_, 2, v___x_2143_);
v___x_2145_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2133_, v___x_2144_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed(lean_object* v_requireType_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
uint8_t v_requireType_boxed_2152_; lean_object* v_res_2153_; 
v_requireType_boxed_2152_ = lean_unbox(v_requireType_2146_);
v_res_2153_ = l_Lean_Parser_Term_strictImplicitBinder_formatter(v_requireType_boxed_2152_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter(uint8_t v_requireType_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2167_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2168_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_formatter___closed__0));
v___x_2169_ = lean_unsigned_to_nat(1024u);
v___x_2170_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0));
v___x_2171_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2172_ = lean_box(v_requireType_2161_);
v___x_2173_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2173_, 0, v___x_2172_);
v___x_2174_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2174_, 0, v___x_2171_);
lean_closure_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2175_, 0, v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2177_, 0, v___x_2175_);
lean_closure_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2178_, 0, v___x_2170_);
lean_closure_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2179_, 0, v___x_2178_);
v___x_2180_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2180_, 0, v___x_2167_);
lean_closure_set(v___x_2180_, 1, v___x_2169_);
lean_closure_set(v___x_2180_, 2, v___x_2179_);
v___x_2181_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2168_, v___x_2180_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter___boxed(lean_object* v_requireType_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
uint8_t v_requireType_boxed_2188_; lean_object* v_res_2189_; 
v_requireType_boxed_2188_ = lean_unbox(v_requireType_2182_);
v_res_2189_ = l_Lean_Parser_Term_implicitBinder_formatter(v_requireType_boxed_2188_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter(lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_formatter___closed__1));
v___x_2201_ = l_Lean_Parser_optional_formatter(v___x_2200_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter___boxed(lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Parser_Term_optIdent_formatter(v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2207_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__2));
v___x_2218_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_formatter___boxed), 5, 0);
v___x_2219_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2219_, 0, v___x_2218_);
lean_closure_set(v___x_2219_, 1, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__2, &l_Lean_Parser_Term_instBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__2);
v___x_2221_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__5(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__4));
v___x_2225_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__3, &l_Lean_Parser_Term_instBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__3);
v___x_2226_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2226_, 0, v___x_2225_);
lean_closure_set(v___x_2226_, 1, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__6(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__5, &l_Lean_Parser_Term_instBinder_formatter___closed__5_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__5);
v___x_2228_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__1));
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2229_, 0, v___x_2228_);
lean_closure_set(v___x_2229_, 1, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__7(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__6, &l_Lean_Parser_Term_instBinder_formatter___closed__6_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__6);
v___x_2231_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__8(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__7, &l_Lean_Parser_Term_instBinder_formatter___closed__7_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__7);
v___x_2233_ = lean_unsigned_to_nat(1024u);
v___x_2234_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2235_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2235_, 0, v___x_2234_);
lean_closure_set(v___x_2235_, 1, v___x_2233_);
lean_closure_set(v___x_2235_, 2, v___x_2232_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter(lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__0));
v___x_2242_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__8, &l_Lean_Parser_Term_instBinder_formatter___closed__8_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__8);
v___x_2243_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2241_, v___x_2242_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter___boxed(lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Parser_Term_instBinder_formatter(v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19(){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2257_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2258_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2259_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0));
v___x_2260_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2261_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2257_, v___x_2258_, v___x_2259_, v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___boxed(lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter(uint8_t v_requireType_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2282_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__2));
v___x_2283_ = lean_box(v_requireType_2276_);
v___x_2284_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2284_, 0, v___x_2283_);
v___x_2285_ = lean_box(v_requireType_2276_);
v___x_2286_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2286_, 0, v___x_2285_);
v___x_2287_ = lean_box(v_requireType_2276_);
v___x_2288_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2288_, 0, v___x_2287_);
v___x_2289_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2290_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2290_, 0, v___x_2288_);
lean_closure_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2291_, 0, v___x_2286_);
lean_closure_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2292_, 0, v___x_2284_);
lean_closure_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2282_, v___x_2292_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object* v_requireType_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
uint8_t v_requireType_boxed_2300_; lean_object* v_res_2301_; 
v_requireType_boxed_2300_ = lean_unbox(v_requireType_2294_);
v_res_2301_ = l_Lean_Parser_Term_bracketedBinder_formatter(v_requireType_boxed_2300_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2301_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_2312_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___boxed), 5, 0);
v___x_2314_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_2315_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2315_, 0, v___x_2314_);
lean_closure_set(v___x_2315_, 1, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3);
v___x_2317_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer(uint8_t v_requireType_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2326_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2327_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0));
v___x_2328_ = lean_unsigned_to_nat(1024u);
v___x_2329_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1));
v___x_2330_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2331_ = lean_box(v_requireType_2320_);
v___x_2332_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4);
v___x_2334_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2334_, 0, v___x_2332_);
lean_closure_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2335_, 0, v___x_2330_);
lean_closure_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2336_, 0, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5));
v___x_2338_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2338_, 0, v___x_2336_);
lean_closure_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2339_, 0, v___x_2329_);
lean_closure_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2340_, 0, v___x_2339_);
v___x_2341_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2341_, 0, v___x_2326_);
lean_closure_set(v___x_2341_, 1, v___x_2328_);
lean_closure_set(v___x_2341_, 2, v___x_2340_);
v___x_2342_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2327_, v___x_2341_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed(lean_object* v_requireType_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v_requireType_boxed_2349_; lean_object* v_res_2350_; 
v_requireType_boxed_2349_ = lean_unbox(v_requireType_2343_);
v_res_2350_ = l_Lean_Parser_Term_explicitBinder_parenthesizer(v_requireType_boxed_2349_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(lean_object* v___x_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_Parser_group_parenthesizer(v___x_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed(lean_object* v___x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(v___x_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___f_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___f_2378_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2));
v___x_2379_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3));
v___x_2380_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2378_, v___x_2379_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed(lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___f_2398_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1));
v___x_2399_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2));
v___x_2400_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2398_, v___x_2399_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed(lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(uint8_t v_requireType_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2420_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2421_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0));
v___x_2422_ = lean_unsigned_to_nat(1024u);
v___x_2423_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed), 5, 0);
v___x_2424_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2425_ = lean_box(v_requireType_2414_);
v___x_2426_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2426_, 0, v___x_2425_);
v___x_2427_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed), 5, 0);
v___x_2428_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2428_, 0, v___x_2426_);
lean_closure_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2429_, 0, v___x_2424_);
lean_closure_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2430_, 0, v___x_2423_);
lean_closure_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2431_, 0, v___x_2430_);
v___x_2432_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2432_, 0, v___x_2420_);
lean_closure_set(v___x_2432_, 1, v___x_2422_);
lean_closure_set(v___x_2432_, 2, v___x_2431_);
v___x_2433_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2421_, v___x_2432_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed(lean_object* v_requireType_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
uint8_t v_requireType_boxed_2440_; lean_object* v_res_2441_; 
v_requireType_boxed_2440_ = lean_unbox(v_requireType_2434_);
v_res_2441_ = l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(v_requireType_boxed_2440_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer(uint8_t v_requireType_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2455_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2456_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0));
v___x_2457_ = lean_unsigned_to_nat(1024u);
v___x_2458_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0));
v___x_2459_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2460_ = lean_box(v_requireType_2449_);
v___x_2461_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2461_, 0, v___x_2460_);
v___x_2462_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2462_, 0, v___x_2459_);
lean_closure_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2463_, 0, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6));
v___x_2465_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2465_, 0, v___x_2463_);
lean_closure_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2466_, 0, v___x_2458_);
lean_closure_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2467_, 0, v___x_2466_);
v___x_2468_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2468_, 0, v___x_2455_);
lean_closure_set(v___x_2468_, 1, v___x_2457_);
lean_closure_set(v___x_2468_, 2, v___x_2467_);
v___x_2469_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2456_, v___x_2468_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed(lean_object* v_requireType_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
uint8_t v_requireType_boxed_2476_; lean_object* v_res_2477_; 
v_requireType_boxed_2476_ = lean_unbox(v_requireType_2470_);
v_res_2477_ = l_Lean_Parser_Term_implicitBinder_parenthesizer(v_requireType_boxed_2476_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer(lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___f_2486_; lean_object* v___x_2487_; 
v___f_2486_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_parenthesizer___closed__0));
v___x_2487_ = l_Lean_Parser_optional_parenthesizer(v___f_2486_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer___boxed(lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_Parser_Term_optIdent_parenthesizer(v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2493_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__1));
v___x_2504_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_parenthesizer___boxed), 5, 0);
v___x_2505_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2505_, 0, v___x_2504_);
lean_closure_set(v___x_2505_, 1, v___x_2503_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2);
v___x_2507_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__4));
v___x_2511_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3);
v___x_2512_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2512_, 0, v___x_2511_);
lean_closure_set(v___x_2512_, 1, v___x_2510_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__5, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5);
v___x_2514_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__1));
v___x_2515_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2515_, 0, v___x_2514_);
lean_closure_set(v___x_2515_, 1, v___x_2513_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__6, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__6_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6);
v___x_2517_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__7, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7);
v___x_2519_ = lean_unsigned_to_nat(1024u);
v___x_2520_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2521_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2521_, 0, v___x_2520_);
lean_closure_set(v___x_2521_, 1, v___x_2519_);
lean_closure_set(v___x_2521_, 2, v___x_2518_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer(lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__0));
v___x_2528_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__8, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8);
v___x_2529_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2527_, v___x_2528_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___boxed(lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_Parser_Term_instBinder_parenthesizer(v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37(){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2543_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2544_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2545_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0));
v___x_2546_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2547_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2543_, v___x_2544_, v___x_2545_, v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___boxed(lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer(uint8_t v_requireType_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2562_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0));
v___x_2563_ = lean_box(v_requireType_2556_);
v___x_2564_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2564_, 0, v___x_2563_);
v___x_2565_ = lean_box(v_requireType_2556_);
v___x_2566_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2566_, 0, v___x_2565_);
v___x_2567_ = lean_box(v_requireType_2556_);
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2568_, 0, v___x_2567_);
v___x_2569_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2570_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2570_, 0, v___x_2568_);
lean_closure_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2571_, 0, v___x_2566_);
lean_closure_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2572_, 0, v___x_2564_);
lean_closure_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2562_, v___x_2572_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object* v_requireType_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
uint8_t v_requireType_boxed_2580_; lean_object* v_res_2581_; 
v_requireType_boxed_2580_ = lean_unbox(v_requireType_2574_);
v_res_2581_ = l_Lean_Parser_Term_bracketedBinder_parenthesizer(v_requireType_boxed_2580_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
return v_res_2581_;
}
}
static lean_object* _init_l_Lean_Parser_Term_bracketedBinder___closed__0(void){
_start:
{
uint8_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2582_ = 1;
v___x_2583_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2584_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__0));
v___x_2585_ = l_Lean_Parser_mkAntiquot(v___x_2584_, v___x_2583_, v___x_2582_, v___x_2582_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t v_requireType_2586_){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2587_ = lean_obj_once(&l_Lean_Parser_Term_bracketedBinder___closed__0, &l_Lean_Parser_Term_bracketedBinder___closed__0_once, _init_l_Lean_Parser_Term_bracketedBinder___closed__0);
v___x_2588_ = l_Lean_Parser_Term_explicitBinder(v_requireType_2586_);
v___x_2589_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_2586_);
v___x_2590_ = l_Lean_Parser_Term_implicitBinder(v_requireType_2586_);
v___x_2591_ = l_Lean_Parser_Term_instBinder;
v___x_2592_ = l_Lean_Parser_orelse(v___x_2590_, v___x_2591_);
v___x_2593_ = l_Lean_Parser_orelse(v___x_2589_, v___x_2592_);
v___x_2594_ = l_Lean_Parser_orelse(v___x_2588_, v___x_2593_);
v___x_2595_ = l_Lean_Parser_withAntiquot(v___x_2587_, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___boxed(lean_object* v_requireType_2596_){
_start:
{
uint8_t v_requireType_boxed_2597_; lean_object* v_res_2598_; 
v_requireType_boxed_2597_ = lean_unbox(v_requireType_2596_);
v_res_2598_ = l_Lean_Parser_Term_bracketedBinder(v_requireType_boxed_2597_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1(){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2602_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0));
v___x_2603_ = l_Lean_addBuiltinDocString(v___x_2601_, v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___boxed(lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter(lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__2));
v___x_2629_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__3));
v___x_2630_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2628_, v___x_2629_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter___boxed(lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Parser_Term_typeSpec_formatter(v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3(){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2644_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2645_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2646_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0));
v___x_2647_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2648_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2644_, v___x_2645_, v___x_2646_, v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___boxed(lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer(lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0));
v___x_2668_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1));
v___x_2669_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2667_, v___x_2668_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___boxed(lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_Parser_Term_typeSpec_parenthesizer(v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7(){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2683_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2684_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2685_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0));
v___x_2686_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2687_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2683_, v___x_2684_, v___x_2685_, v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___boxed(lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
return v_res_2689_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__0(void){
_start:
{
uint8_t v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = 0;
v___x_2691_ = 1;
v___x_2692_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2693_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__0));
v___x_2694_ = l_Lean_Parser_mkAntiquot(v___x_2693_, v___x_2692_, v___x_2691_, v___x_2690_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__1(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2695_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_2696_ = lean_unsigned_to_nat(1024u);
v___x_2697_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2698_ = l_Lean_Parser_leadingNode(v___x_2697_, v___x_2696_, v___x_2695_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__2(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__1, &l_Lean_Parser_Term_typeSpec___closed__1_once, _init_l_Lean_Parser_Term_typeSpec___closed__1);
v___x_2700_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__0, &l_Lean_Parser_Term_typeSpec___closed__0_once, _init_l_Lean_Parser_Term_typeSpec___closed__0);
v___x_2701_ = l_Lean_Parser_withAntiquot(v___x_2700_, v___x_2699_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__3(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__2, &l_Lean_Parser_Term_typeSpec___closed__2_once, _init_l_Lean_Parser_Term_typeSpec___closed__2);
v___x_2703_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2704_ = l_Lean_Parser_withCache(v___x_2703_, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec(void){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__3, &l_Lean_Parser_Term_typeSpec___closed__3_once, _init_l_Lean_Parser_Term_typeSpec___closed__3);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter(lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2712_ = l_Lean_Parser_optional_formatter(v___x_2711_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter___boxed(lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Parser_Term_optType_formatter(v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer(lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2725_ = l_Lean_Parser_optional_parenthesizer(v___x_2724_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer___boxed(lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Parser_Term_optType_parenthesizer(v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
return v_res_2731_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType___closed__0(void){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = l_Lean_Parser_Term_typeSpec;
v___x_2733_ = l_Lean_Parser_optional(v___x_2732_);
return v___x_2733_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType(void){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_obj_once(&l_Lean_Parser_Term_optType___closed__0, &l_Lean_Parser_Term_optType___closed__0_once, _init_l_Lean_Parser_Term_optType___closed__0);
return v___x_2734_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_unsigned_to_nat(2382944618u);
v___x_2766_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2767_ = l_Lean_Name_num___override(v___x_2766_, v___x_2765_);
return v___x_2767_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2769_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2770_ = l_Lean_Name_str___override(v___x_2769_, v___x_2768_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2772_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2773_ = l_Lean_Name_str___override(v___x_2772_, v___x_2771_);
return v___x_2773_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = lean_unsigned_to_nat(2u);
v___x_2775_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2776_ = l_Lean_Name_num___override(v___x_2775_, v___x_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2779_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2780_ = 0;
v___x_2781_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2782_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_2778_, v___x_2779_, v___x_2780_, v___x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2____boxed(lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser(lean_object* v_rbp_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_2789_ = l_Lean_Parser_categoryParser(v___x_2788_, v_rbp_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter(lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__2));
v___x_2818_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__6));
v___x_2819_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2817_, v___x_2818_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter___boxed(lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Parser_Term_optEllipsis_formatter(v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3(){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2833_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2834_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2835_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0));
v___x_2836_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_formatter___boxed), 5, 0);
v___x_2837_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2833_, v___x_2834_, v___x_2835_, v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___boxed(lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer(lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2860_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0));
v___x_2861_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3));
v___x_2862_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2860_, v___x_2861_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed(lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Parser_Term_optEllipsis_parenthesizer(v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7(){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2876_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2877_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2878_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0));
v___x_2879_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed), 5, 0);
v___x_2880_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2876_, v___x_2877_, v___x_2878_, v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___boxed(lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
return v_res_2882_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__0(void){
_start:
{
uint8_t v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2883_ = 0;
v___x_2884_ = 1;
v___x_2885_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2886_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__0));
v___x_2887_ = l_Lean_Parser_mkAntiquot(v___x_2886_, v___x_2885_, v___x_2884_, v___x_2883_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__1(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__3));
v___x_2889_ = l_Lean_Parser_symbol(v___x_2888_);
return v___x_2889_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__2(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__1, &l_Lean_Parser_Term_optEllipsis___closed__1_once, _init_l_Lean_Parser_Term_optEllipsis___closed__1);
v___x_2891_ = l_Lean_Parser_optional(v___x_2890_);
return v___x_2891_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__3(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__2, &l_Lean_Parser_Term_optEllipsis___closed__2_once, _init_l_Lean_Parser_Term_optEllipsis___closed__2);
v___x_2893_ = lean_unsigned_to_nat(1024u);
v___x_2894_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2895_ = l_Lean_Parser_leadingNode(v___x_2894_, v___x_2893_, v___x_2892_);
return v___x_2895_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__4(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__3, &l_Lean_Parser_Term_optEllipsis___closed__3_once, _init_l_Lean_Parser_Term_optEllipsis___closed__3);
v___x_2897_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__0, &l_Lean_Parser_Term_optEllipsis___closed__0_once, _init_l_Lean_Parser_Term_optEllipsis___closed__0);
v___x_2898_ = l_Lean_Parser_withAntiquot(v___x_2897_, v___x_2896_);
return v___x_2898_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__5(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__4, &l_Lean_Parser_Term_optEllipsis___closed__4_once, _init_l_Lean_Parser_Term_optEllipsis___closed__4);
v___x_2900_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2901_ = l_Lean_Parser_withCache(v___x_2900_, v___x_2899_);
return v___x_2901_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis(void){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__5, &l_Lean_Parser_Term_optEllipsis___closed__5_once, _init_l_Lean_Parser_Term_optEllipsis___closed__5);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter(lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2));
v___x_2934_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6));
v___x_2935_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2933_, v___x_2934_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___boxed(lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Parser_Term_structInstArrayRef_formatter(v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3(){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2949_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2950_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_2951_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0));
v___x_2952_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_2953_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2949_, v___x_2950_, v___x_2951_, v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___boxed(lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer(lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0));
v___x_2981_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4));
v___x_2982_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2980_, v___x_2981_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed(lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Parser_Term_structInstArrayRef_parenthesizer(v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7(){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2996_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2997_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_2998_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0));
v___x_2999_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3000_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2996_, v___x_2997_, v___x_2998_, v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___boxed(lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
return v_res_3002_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__0(void){
_start:
{
uint8_t v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3003_ = 0;
v___x_3004_ = 1;
v___x_3005_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3006_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0));
v___x_3007_ = l_Lean_Parser_mkAntiquot(v___x_3006_, v___x_3005_, v___x_3004_, v___x_3003_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__1(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_3009_ = l_Lean_Parser_withoutPosition(v___x_3008_);
return v___x_3009_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__2(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_3011_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__1, &l_Lean_Parser_Term_structInstArrayRef___closed__1_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__1);
v___x_3012_ = l_Lean_Parser_andthen(v___x_3011_, v___x_3010_);
return v___x_3012_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__3(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__2, &l_Lean_Parser_Term_structInstArrayRef___closed__2_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__2);
v___x_3014_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_3015_ = l_Lean_Parser_andthen(v___x_3014_, v___x_3013_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__4(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__3, &l_Lean_Parser_Term_structInstArrayRef___closed__3_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__3);
v___x_3017_ = lean_unsigned_to_nat(1024u);
v___x_3018_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3019_ = l_Lean_Parser_leadingNode(v___x_3018_, v___x_3017_, v___x_3016_);
return v___x_3019_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__5(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__4, &l_Lean_Parser_Term_structInstArrayRef___closed__4_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__4);
v___x_3021_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__0, &l_Lean_Parser_Term_structInstArrayRef___closed__0_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__0);
v___x_3022_ = l_Lean_Parser_withAntiquot(v___x_3021_, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__6(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__5, &l_Lean_Parser_Term_structInstArrayRef___closed__5_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__5);
v___x_3024_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3025_ = l_Lean_Parser_withCache(v___x_3024_, v___x_3023_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef(void){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__6, &l_Lean_Parser_Term_structInstArrayRef___closed__6_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__6);
return v___x_3026_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3041_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3042_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3042_, 0, v___x_3041_);
lean_closure_set(v___x_3042_, 1, v___x_3040_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__3, &l_Lean_Parser_Term_structInstLVal_formatter___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3);
v___x_3044_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3045_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3045_, 0, v___x_3044_);
lean_closure_set(v___x_3045_, 1, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3050_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3051_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3051_, 0, v___x_3050_);
lean_closure_set(v___x_3051_, 1, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__7, &l_Lean_Parser_Term_structInstLVal_formatter___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7);
v___x_3053_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__6));
v___x_3054_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3054_, 0, v___x_3053_);
lean_closure_set(v___x_3054_, 1, v___x_3052_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__8, &l_Lean_Parser_Term_structInstLVal_formatter___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8);
v___x_3056_ = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter___boxed), 6, 1);
lean_closure_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3058_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__9, &l_Lean_Parser_Term_structInstLVal_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9);
v___x_3059_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3059_, 0, v___x_3058_);
lean_closure_set(v___x_3059_, 1, v___x_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__10, &l_Lean_Parser_Term_structInstLVal_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10);
v___x_3061_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3061_, 0, v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__11, &l_Lean_Parser_Term_structInstLVal_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11);
v___x_3063_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__4, &l_Lean_Parser_Term_structInstLVal_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4);
v___x_3064_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3064_, 0, v___x_3063_);
lean_closure_set(v___x_3064_, 1, v___x_3062_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3065_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__12, &l_Lean_Parser_Term_structInstLVal_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12);
v___x_3066_ = lean_unsigned_to_nat(1024u);
v___x_3067_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3068_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3068_, 0, v___x_3067_);
lean_closure_set(v___x_3068_, 1, v___x_3066_);
lean_closure_set(v___x_3068_, 2, v___x_3065_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter(lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__2));
v___x_3075_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__13, &l_Lean_Parser_Term_structInstLVal_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13);
v___x_3076_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3074_, v___x_3075_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter___boxed(lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_Parser_Term_structInstLVal_formatter(v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3(){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3090_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3091_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3092_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0));
v___x_3093_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3094_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3090_, v___x_3091_, v___x_3092_, v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___boxed(lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_3098_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0___boxed(lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
return v_res_3108_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; 
v___x_3117_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___f_3118_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0));
v___x_3119_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3119_, 0, v___f_3118_);
lean_closure_set(v___x_3119_, 1, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2);
v___x_3121_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_3122_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3122_, 0, v___x_3121_);
lean_closure_set(v___x_3122_, 1, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3134_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7));
v___x_3135_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3135_, 0, v___x_3134_);
lean_closure_set(v___x_3135_, 1, v___x_3133_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8);
v___x_3137_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9);
v___x_3139_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3);
v___x_3140_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3140_, 0, v___x_3139_);
lean_closure_set(v___x_3140_, 1, v___x_3138_);
return v___x_3140_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3141_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10);
v___x_3142_ = lean_unsigned_to_nat(1024u);
v___x_3143_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3144_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3144_, 0, v___x_3143_);
lean_closure_set(v___x_3144_, 1, v___x_3142_);
lean_closure_set(v___x_3144_, 2, v___x_3141_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer(lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1));
v___x_3151_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11);
v___x_3152_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3150_, v___x_3151_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed(lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_Parser_Term_structInstLVal_parenthesizer(v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7(){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3166_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3167_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3168_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0));
v___x_3169_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3170_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3166_, v___x_3167_, v___x_3168_, v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___boxed(lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
return v_res_3172_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__0(void){
_start:
{
uint8_t v___x_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3173_ = 0;
v___x_3174_ = 1;
v___x_3175_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3176_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__0));
v___x_3177_ = l_Lean_Parser_mkAntiquot(v___x_3176_, v___x_3175_, v___x_3174_, v___x_3173_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__1(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3179_ = l_Lean_Parser_fieldIdx;
v___x_3180_ = l_Lean_Parser_orelse(v___x_3179_, v___x_3178_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__2(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__1, &l_Lean_Parser_Term_structInstLVal___closed__1_once, _init_l_Lean_Parser_Term_structInstLVal___closed__1);
v___x_3182_ = l_Lean_Parser_ident;
v___x_3183_ = l_Lean_Parser_orelse(v___x_3182_, v___x_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__3(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__5));
v___x_3185_ = l_Lean_Parser_symbol(v___x_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__4(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = l_Lean_Parser_fieldIdx;
v___x_3187_ = l_Lean_Parser_ident;
v___x_3188_ = l_Lean_Parser_orelse(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__5(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__4, &l_Lean_Parser_Term_structInstLVal___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal___closed__4);
v___x_3190_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__3, &l_Lean_Parser_Term_structInstLVal___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal___closed__3);
v___x_3191_ = l_Lean_Parser_andthen(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__6(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__5, &l_Lean_Parser_Term_structInstLVal___closed__5_once, _init_l_Lean_Parser_Term_structInstLVal___closed__5);
v___x_3193_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_3194_ = l_Lean_Parser_node(v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__7(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3196_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__6, &l_Lean_Parser_Term_structInstLVal___closed__6_once, _init_l_Lean_Parser_Term_structInstLVal___closed__6);
v___x_3197_ = l_Lean_Parser_orelse(v___x_3196_, v___x_3195_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__8(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__7, &l_Lean_Parser_Term_structInstLVal___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal___closed__7);
v___x_3199_ = l_Lean_Parser_many(v___x_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__9(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__8, &l_Lean_Parser_Term_structInstLVal___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal___closed__8);
v___x_3201_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__2, &l_Lean_Parser_Term_structInstLVal___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal___closed__2);
v___x_3202_ = l_Lean_Parser_andthen(v___x_3201_, v___x_3200_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__10(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3203_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__9, &l_Lean_Parser_Term_structInstLVal___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal___closed__9);
v___x_3204_ = lean_unsigned_to_nat(1024u);
v___x_3205_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3206_ = l_Lean_Parser_leadingNode(v___x_3205_, v___x_3204_, v___x_3203_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__11(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__10, &l_Lean_Parser_Term_structInstLVal___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal___closed__10);
v___x_3208_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__0, &l_Lean_Parser_Term_structInstLVal___closed__0_once, _init_l_Lean_Parser_Term_structInstLVal___closed__0);
v___x_3209_ = l_Lean_Parser_withAntiquot(v___x_3208_, v___x_3207_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__12(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__11, &l_Lean_Parser_Term_structInstLVal___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal___closed__11);
v___x_3211_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3212_ = l_Lean_Parser_withCache(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal(void){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__12, &l_Lean_Parser_Term_structInstLVal___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal___closed__12);
return v___x_3213_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3));
v___x_3230_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_3231_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3231_, 0, v___x_3230_);
lean_closure_set(v___x_3231_, 1, v___x_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter(lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2));
v___x_3238_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4, &l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4);
v___x_3239_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3237_, v___x_3238_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed(lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Parser_Term_structInstFieldBinder_formatter(v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
return v_res_3245_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1));
v___x_3256_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_3257_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3257_, 0, v___x_3256_);
lean_closure_set(v___x_3257_, 1, v___x_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0));
v___x_3264_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2);
v___x_3265_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3263_, v___x_3264_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed(lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3271_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0(void){
_start:
{
uint8_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3272_ = 1;
v___x_3273_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1));
v___x_3274_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0));
v___x_3275_ = l_Lean_Parser_mkAntiquot(v___x_3274_, v___x_3273_, v___x_3272_, v___x_3272_);
return v___x_3275_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1(void){
_start:
{
uint8_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = 0;
v___x_3277_ = l_Lean_Parser_Term_bracketedBinder(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__1, &l_Lean_Parser_Term_structInstFieldBinder___closed__1_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1);
v___x_3279_ = l_Lean_Parser_Term_binderIdent;
v___x_3280_ = l_Lean_Parser_orelse(v___x_3279_, v___x_3278_);
return v___x_3280_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__2, &l_Lean_Parser_Term_structInstFieldBinder___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2);
v___x_3282_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__0, &l_Lean_Parser_Term_structInstFieldBinder___closed__0_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0);
v___x_3283_ = l_Lean_Parser_withAntiquot(v___x_3282_, v___x_3281_);
return v___x_3283_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder(void){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__3, &l_Lean_Parser_Term_structInstFieldBinder___closed__3_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3);
return v___x_3284_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0));
v___x_3288_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_3289_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3289_, 0, v___x_3288_);
lean_closure_set(v___x_3289_, 1, v___x_3287_);
return v___x_3289_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1);
v___x_3291_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter(lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2);
v___x_3298_ = l_Lean_Parser_optional_formatter(v___x_3297_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed(lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Parser_Term_optTypeForStructInst_formatter(v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3304_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___f_3309_; 
v___x_3307_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0));
v___x_3308_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___f_3309_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3309_, 0, v___x_3308_);
lean_closure_set(v___f_3309_, 1, v___x_3307_);
return v___f_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v___f_3315_; lean_object* v___x_3316_; 
v___f_3315_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1);
v___x_3316_ = l_Lean_Parser_optional_parenthesizer(v___f_3315_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed(lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
return v_res_3322_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_3324_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_3325_ = l_Lean_Parser_notFollowedBy(v___x_3324_, v___x_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__0, &l_Lean_Parser_Term_optTypeForStructInst___closed__0_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0);
v___x_3327_ = l_Lean_Parser_Term_typeSpec;
v___x_3328_ = l_Lean_Parser_andthen(v___x_3327_, v___x_3326_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__1, &l_Lean_Parser_Term_optTypeForStructInst___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1);
v___x_3330_ = l_Lean_Parser_atomic(v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__2, &l_Lean_Parser_Term_optTypeForStructInst___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2);
v___x_3332_ = l_Lean_Parser_optional(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst(void){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__3, &l_Lean_Parser_Term_optTypeForStructInst___closed__3_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3340_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_3339_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg___boxed(lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter(lean_object* v_rbp_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___boxed(lean_object* v_rbp_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter(v_rbp_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_rbp_3354_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0(lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3362_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0___boxed(lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Parser_Term_structInstField_formatter___lam__0(v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1(lean_object* v___x_3373_, lean_object* v___x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3373_, v___x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed(lean_object* v___x_3381_, lean_object* v___x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Parser_Term_structInstField_formatter___lam__1(v___x_3381_, v___x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3388_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__4(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed), 5, 0);
v___f_3404_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__0));
v___x_3405_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3405_, 0, v___f_3404_);
lean_closure_set(v___x_3405_, 1, v___x_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__5(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__4, &l_Lean_Parser_Term_structInstField_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__4);
v___x_3407_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_3408_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3408_, 0, v___x_3407_);
lean_closure_set(v___x_3408_, 1, v___x_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__6(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__5, &l_Lean_Parser_Term_structInstField_formatter___closed__5_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__5);
v___x_3410_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__9(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__8));
v___x_3416_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed), 5, 0);
v___x_3417_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3417_, 0, v___x_3416_);
lean_closure_set(v___x_3417_, 1, v___x_3415_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__10(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__9, &l_Lean_Parser_Term_structInstField_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__9);
v___x_3419_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__6, &l_Lean_Parser_Term_structInstField_formatter___closed__6_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__6);
v___x_3420_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3420_, 0, v___x_3419_);
lean_closure_set(v___x_3420_, 1, v___x_3418_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__11(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__10, &l_Lean_Parser_Term_structInstField_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__10);
v___x_3422_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__12(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__11, &l_Lean_Parser_Term_structInstField_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__11);
v___x_3424_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3425_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3425_, 0, v___x_3424_);
lean_closure_set(v___x_3425_, 1, v___x_3423_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__13(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3426_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__12, &l_Lean_Parser_Term_structInstField_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__12);
v___x_3427_ = lean_unsigned_to_nat(1024u);
v___x_3428_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3429_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3429_, 0, v___x_3428_);
lean_closure_set(v___x_3429_, 1, v___x_3427_);
lean_closure_set(v___x_3429_, 2, v___x_3426_);
return v___x_3429_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__14(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___f_3432_; 
v___x_3430_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__13, &l_Lean_Parser_Term_structInstField_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__13);
v___x_3431_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__3));
v___f_3432_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed), 7, 2);
lean_closure_set(v___f_3432_, 0, v___x_3431_);
lean_closure_set(v___f_3432_, 1, v___x_3430_);
return v___f_3432_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__15(void){
_start:
{
lean_object* v___f_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___f_3433_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__14, &l_Lean_Parser_Term_structInstField_formatter___closed__14_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__14);
v___x_3434_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3435_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_formatter___boxed), 7, 2);
lean_closure_set(v___x_3435_, 0, v___x_3434_);
lean_closure_set(v___x_3435_, 1, v___f_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter(lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__15, &l_Lean_Parser_Term_structInstField_formatter___closed__15_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__15);
v___x_3442_ = l_Lean_Parser_ppGroup_formatter(v___x_3441_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Parser_Term_structInstField_formatter(v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5(){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3456_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3457_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3458_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0));
v___x_3459_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___boxed), 5, 0);
v___x_3460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3456_, v___x_3457_, v___x_3458_, v___x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___boxed(lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(lean_object* v_rbp_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3470_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_3469_, v_rbp_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer___boxed(lean_object* v_rbp_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(v_rbp_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
return v_res_3477_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed), 5, 0);
v___x_3487_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__1));
v___x_3488_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3488_, 0, v___x_3487_);
lean_closure_set(v___x_3488_, 1, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2);
v___x_3490_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_3491_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3491_, 0, v___x_3490_);
lean_closure_set(v___x_3491_, 1, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3);
v___x_3493_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3493_, 0, v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__6));
v___x_3499_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed), 5, 0);
v___x_3500_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3500_, 0, v___x_3499_);
lean_closure_set(v___x_3500_, 1, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__7, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7);
v___x_3502_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__4, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4);
v___x_3503_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3503_, 0, v___x_3502_);
lean_closure_set(v___x_3503_, 1, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8);
v___x_3505_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9);
v___x_3507_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3508_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3508_, 0, v___x_3507_);
lean_closure_set(v___x_3508_, 1, v___x_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3509_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10);
v___x_3510_ = lean_unsigned_to_nat(1024u);
v___x_3511_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3512_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3512_, 0, v___x_3511_);
lean_closure_set(v___x_3512_, 1, v___x_3510_);
lean_closure_set(v___x_3512_, 2, v___x_3509_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11);
v___x_3514_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__0));
v___x_3515_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3515_, 0, v___x_3514_);
lean_closure_set(v___x_3515_, 1, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__12, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__12_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12);
v___x_3517_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3518_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3518_, 0, v___x_3517_);
lean_closure_set(v___x_3518_, 1, v___x_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer(lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__13, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__13_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13);
v___x_3525_ = l_Lean_Parser_ppGroup_parenthesizer(v___x_3524_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lean_Parser_Term_structInstField_parenthesizer(v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11(){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3539_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3540_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3541_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0));
v___x_3542_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_parenthesizer___boxed), 5, 0);
v___x_3543_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3539_, v___x_3540_, v___x_3541_, v___x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___boxed(lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
return v_res_3545_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__0(void){
_start:
{
uint8_t v___x_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3546_ = 0;
v___x_3547_ = 1;
v___x_3548_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3549_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__1));
v___x_3550_ = l_Lean_Parser_mkAntiquot(v___x_3549_, v___x_3548_, v___x_3547_, v___x_3546_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__2(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l_Lean_Parser_Term_structInstField___closed__1));
v___x_3553_ = l_Lean_Parser_checkColGt(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__3(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = l_Lean_Parser_Term_structInstFieldBinder;
v___x_3555_ = l_Lean_Parser_skip;
v___x_3556_ = l_Lean_Parser_andthen(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__4(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__3, &l_Lean_Parser_Term_structInstField___closed__3_once, _init_l_Lean_Parser_Term_structInstField___closed__3);
v___x_3558_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__2, &l_Lean_Parser_Term_structInstField___closed__2_once, _init_l_Lean_Parser_Term_structInstField___closed__2);
v___x_3559_ = l_Lean_Parser_andthen(v___x_3558_, v___x_3557_);
return v___x_3559_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__5(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__4, &l_Lean_Parser_Term_structInstField___closed__4_once, _init_l_Lean_Parser_Term_structInstField___closed__4);
v___x_3561_ = l_Lean_Parser_many(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__6(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3564_ = l_Lean_Parser_categoryParser(v___x_3563_, v___x_3562_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__7(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__6, &l_Lean_Parser_Term_structInstField___closed__6_once, _init_l_Lean_Parser_Term_structInstField___closed__6);
v___x_3566_ = l_Lean_Parser_Term_optTypeForStructInst;
v___x_3567_ = l_Lean_Parser_andthen(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__8(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__7, &l_Lean_Parser_Term_structInstField___closed__7_once, _init_l_Lean_Parser_Term_structInstField___closed__7);
v___x_3569_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__5, &l_Lean_Parser_Term_structInstField___closed__5_once, _init_l_Lean_Parser_Term_structInstField___closed__5);
v___x_3570_ = l_Lean_Parser_andthen(v___x_3569_, v___x_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__9(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__8, &l_Lean_Parser_Term_structInstField___closed__8_once, _init_l_Lean_Parser_Term_structInstField___closed__8);
v___x_3572_ = l_Lean_Parser_optional(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__10(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__9, &l_Lean_Parser_Term_structInstField___closed__9_once, _init_l_Lean_Parser_Term_structInstField___closed__9);
v___x_3574_ = l_Lean_Parser_Term_structInstLVal;
v___x_3575_ = l_Lean_Parser_andthen(v___x_3574_, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__11(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3576_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__10, &l_Lean_Parser_Term_structInstField___closed__10_once, _init_l_Lean_Parser_Term_structInstField___closed__10);
v___x_3577_ = lean_unsigned_to_nat(1024u);
v___x_3578_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3579_ = l_Lean_Parser_leadingNode(v___x_3578_, v___x_3577_, v___x_3576_);
return v___x_3579_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__12(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__11, &l_Lean_Parser_Term_structInstField___closed__11_once, _init_l_Lean_Parser_Term_structInstField___closed__11);
v___x_3581_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__0, &l_Lean_Parser_Term_structInstField___closed__0_once, _init_l_Lean_Parser_Term_structInstField___closed__0);
v___x_3582_ = l_Lean_Parser_withAntiquot(v___x_3581_, v___x_3580_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__13(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__12, &l_Lean_Parser_Term_structInstField___closed__12_once, _init_l_Lean_Parser_Term_structInstField___closed__12);
v___x_3584_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3585_ = l_Lean_Parser_withCache(v___x_3584_, v___x_3583_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField(void){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__13, &l_Lean_Parser_Term_structInstField___closed__13_once, _init_l_Lean_Parser_Term_structInstField___closed__13);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object* v_p_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3600_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_3599_, v_p_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter___boxed(lean_object* v_p_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_Parser_Term_structInstFields_formatter(v_p_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object* v_p_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3615_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_3614_, v_p_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer___boxed(lean_object* v_p_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v_p_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields(lean_object* v_p_3623_){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3625_ = l_Lean_Parser_node(v___x_3624_, v_p_3623_);
return v___x_3625_;
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
