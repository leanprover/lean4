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
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
extern lean_object* l_Lean_Parser_fieldIdx;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppDedent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sepByIndentSemicolon"};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(170, 99, 196, 249, 102, 11, 22, 231)}};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "`sepByIndentSemicolon(p)` parses a sequence of `p` optionally followed by `;`,\nsimilar to `manyIndent(p \";\"\?)`, except that if two occurrences of `p` occur on the same line,\nthe `;` is mandatory. This is used by tactic parsing, so that\n```\nexample := by\n  skip\n  skip\n```\nis legal, but `by skip skip` is not - it must be written as `by skip; skip`. "};
static const lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sepBy1IndentSemicolon"};
static const lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 122, 81, 170, 140, 136, 141, 66)}};
static const lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 363, .m_capacity = 363, .m_length = 362, .m_data = "`sepBy1IndentSemicolon(p)` parses a (nonempty) sequence of `p` optionally followed by `;`,\nsimilar to `many1Indent(p \";\"\?)`, except that if two occurrences of `p` occur on the same line,\nthe `;` is mandatory. This is used by tactic parsing, so that\n```\nexample := by\n  skip\n  skip\n```\nis legal, but `by skip skip` is not - it must be written as `by skip; skip`. "};
static const lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 141, 160, 225, 89, 107, 71, 117)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepByIndentSemicolon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2_value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 113, 252, 92, 83, 246, 160, 172)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1_value)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 133, .m_capacity = 133, .m_length = 131, .m_data = "The syntax `{ tacs }` is an alternative syntax for `· tacs`.\nIt runs the tactics in sequence, and fails if the goal is not solved. "};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 28, 43, 150, 183, 142, 81, 15)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 209, 129, 56, 116, 223, 51, 73)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 70, 11, 167, 226, 145, 9, 201)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 119, 215, 182, 191, 114, 165, 30)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_sepBy1IndentSemicolon_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 13, 185, 142, 76, 107, 137, 177)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 229, 96, 2, 142, 147, 226, 101)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 166, .m_capacity = 166, .m_length = 165, .m_data = "A sequence of tactics in brackets, or a delimiter-free indented sequence of tactics.\nDelimiter-free indentation is determined by the *first* tactic of the sequence. "};
static const lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticSeqIndentGt"};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 164, 99, 10, 143, 215, 5, 182)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 71, 140, 7, 47, 84, 129, 16)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 207, .m_capacity = 207, .m_length = 206, .m_data = "Same as [`tacticSeq`] but requires delimiter-free tactic sequence to have strict indentation.\nThe strict indentation requirement only apply to *nested* `by`s, as top-level `by`s do not have a\nposition set. "};
static const lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_seq1_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Lean_Parser_Tactic_seq1_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 140, 213, 31, 38, 205, 32, 123)}};
static const lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_seq1_parenthesizer___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_seq1_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_ctor_object l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 68, 6, 57, 113, 151, 68, 138)}};
static const lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 814, .m_capacity = 814, .m_length = 813, .m_data = "A *hole* (or *placeholder term*), which stands for an unknown term that is expected to be inferred based on context.\nFor example, in `@id _ Nat.zero`, the `_` must be the type of `Nat.zero`, which is `Nat`.\n\nThe way this works is that holes create fresh metavariables.\nThe elaborator is allowed to assign terms to metavariables while it is checking definitional equalities.\nThis is often known as *unification*.\n\nNormally, all holes must be solved for. However, there are a few contexts where this is not necessary:\n* In `match` patterns, holes are catch-all patterns.\n* In some tactics, such as `refine'` and `apply`, unsolved-for placeholders become new goals.\n\nRelated concept: implicit parameters are automatically filled in with holes during the elaboration process.\n\nSee also `\?m` syntax (synthetic holes).\n"};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(144) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__4_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__2_value),((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_hole_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_hole_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_hole_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_hole_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_hole_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_hole_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_hole_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 229, 9, 16, 12, 224, 229, 201)}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_hole_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_hole_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_hole_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_hole_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_hole_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_hole_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_hole_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_ctor_object l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 251, 253, 165, 169, 88, 32, 49)}};
static const lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0 = (const lean_object*)&l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3166, .m_capacity = 3166, .m_length = 3151, .m_data = "A *synthetic hole* (or *synthetic placeholder*), which stands for an unknown term that should be synthesized using tactics.\n- `\?_` creates a fresh metavariable with an auto-generated name.\n- `\?m` either refers to a pre-existing metavariable named `m` or creates a fresh metavariable with that name.\n\nIn particular, the synthetic hole syntax creates \"synthetic opaque metavariables\",\nthe same kind of metavariable used to represent goals in the tactic state.\n\nSynthetic holes are similar to holes in that `_` also creates metavariables,\nbut synthetic opaque metavariables have some different properties:\n- In tactics such as `refine`, only synthetic holes yield new goals.\n- During elaboration, unification will not solve for synthetic opaque metavariables, they are \"opaque\".\n  This is to prevent counterintuitive behavior such as disappearing goals.\n- When synthetic holes appear under binders, they capture local variables using a more complicated mechanism known as delayed assignment.\n\n## Delayed assigned metavariables\n\nThis section gives an overview of some technical details of synthetic holes, which you should feel free to skip.\nUnderstanding delayed assignments is mainly useful for those who are working on tactics and other metaprogramming.\nIt is included here until there is a suitable place for it in the reference manual.\n\nWhen a synthetic hole appears under a binding construct, such as for example `fun (x : α) (y : β) => \?s`,\nthe system creates a *delayed assignment*. This consists of\n1. A metavariable `\?m` of type `(x : α) → (y : β) → γ x y` whose local context is the local context outside the `fun`,\n  where `γ x y` is the type of `\?s`. Recall that `x` and `y` appear in the local context of `\?s`.\n2. A delayed assignment record associating `\?m` to `\?s` and the variables `#[x, y]` in the local context of `\?s`\n\nThen, this function elaborates as `fun (x : α) (y : β) => \?m x y`, where one should understand `x` and `y` here\nas being De Bruijn indexes, since Lean uses the locally nameless encoding of lambda calculus.\n\nOnce `\?s` is fully solved for, in the sense that after metavariable instantiation it is a metavariable-free term `e`,\nthen we can make the assignment `\?m := fun (x' : α) (y' : β) => e[x := x', y := y']`.\n(Implementation note: Lean only instantiates full applications `\?m x' y'` of delayed assigned metavariables, to skip forming this function.)\nThis delayed assignment mechanism is essential to the operation of basic tactics like `intro`,\nand a good mental model is that it is a way to \"apply\" the metavariable `\?s` by substituting values in for some of its local variables.\nWhile it would be easier to immediately assign `\?s := \?m x y`,\ndelayed assignment preserves `\?s` as an unsolved-for metavariable with a local context that still contains `x` and `y`,\nwhich is exactly what tactics like `intro` need.\n\nBy default, delayed assigned metavariables pretty print with what they are delayed assigned to.\nThe delayed assigned metavariables themselves can be pretty printed using `set_option pp.mvars.delayed true`.\n\nFor more information, see the \"Gruesome details\" module docstrings in `Lean.MetavarContext`.\n"};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(148) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__4_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__2_value),((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 87, 196, 54, 9, 128, 178, 139)}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_syntheticHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 25, 118, 219, 8, 203, 22, 194)}};
static const lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0 = (const lean_object*)&l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 435, .m_capacity = 435, .m_length = 428, .m_data = "The `⋯` term denotes a term that was omitted by the pretty printer.\nThe presence of `⋯` in pretty printer output is controlled by the `pp.deepTerms` and `pp.proofs` options,\nand these options can be further adjusted using `pp.deepTerms.threshold` and `pp.proofs.threshold`.\n\nIt is only meant to be used for pretty printing.\nHowever, in case it is copied and pasted from the Infoview, `⋯` logs a warning and elaborates like `_`.\n"};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(158) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__2_value),((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_omission_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_omission_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_omission_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_omission_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_omission_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_omission_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_omission_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 172, 62, 233, 244, 85, 47, 109)}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_omission_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_omission_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_omission_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__3_value)} };
static const lean_object* l_Lean_Parser_Term_omission_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_omission_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_omission_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Term_omission_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_omission___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_ctor_object l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 133, 194, 146, 208, 209, 34, 77)}};
static const lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0 = (const lean_object*)&l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 165, 164, 143, 129, 158, 74, 4)}};
static const lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 181, 78, 34, 190, 12, 180, 92)}};
static const lean_ctor_object l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 3, 105, 152, 28, 10, 167, 0)}};
static const lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 147, .m_capacity = 147, .m_length = 146, .m_data = "Explicit binder, like `(x y : A)` or `(x y)`.\nDefault values can be specified using `(x : A := v)` syntax, and tactics using `(x : A := by tac)`.\n"};
static const lean_object* l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 379, .m_capacity = 379, .m_length = 378, .m_data = "Implicit binder, like `{x y : A}` or `{x y}`.\nIn regular applications, whenever all parameters before it have been specified,\nthen a `_` placeholder is automatically inserted for this parameter.\nImplicit parameters should be able to be determined from the other arguments and the return type\nby unification.\n\nIn `@` explicit mode, implicit binders behave like explicit binders.\n"};
static const lean_object* l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 783, .m_capacity = 783, .m_length = 752, .m_data = "Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`.\nIn contrast to `{ ... }` implicit binders, strict-implicit binders do not automatically insert\na `_` placeholder until at least one subsequent explicit parameter is specified.\nDo *not* use strict-implicit binders unless there is a subsequent explicit parameter.\nAssuming this rule is followed, for fully applied expressions implicit and strict-implicit binders have the same behavior.\n\nExample: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`,\nthen `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter,\nand `h hs` has type `p y`.\nIn contrast, if `h' : ∀ {x : A}, x ∈ s → p x`, then `h` by itself elaborates to have type `\?m ∈ s → p \?m`\nwith `\?m` a fresh metavariable.\n"};
static const lean_object* l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 430, .m_capacity = 430, .m_length = 429, .m_data = "Instance-implicit binder, like `[C]` or `[inst : C]`.\nIn regular applications without `@` explicit mode, it is automatically inserted\nand solved for by typeclass inference for the specified class `C`.\nIn `@` explicit mode, if `_` is used for an instance-implicit parameter, then it is still solved for by typeclass inference;\nuse `(_)` to inhibit this and have it be solved for by unification instead, like an implicit argument.\n"};
static const lean_object* l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_binderDefault_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__0_value),((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_binderDefault_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_binderDefault_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderTactic_formatter___closed__4_value),((lean_object*)&l_Lean_Parser_Term_binderType_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_binderDefault_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Term_binderDefault_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Term_binderDefault_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Term_binderDefault_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_binderDefault___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 119, 214, 97, 198, 223, 242, 31)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 200, 15, 206, 200, 98, 47, 188)}};
static const lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2;
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
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 181, 168, 154, 36, 105, 180, 29)}};
static const lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2;
static const lean_closure_object l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5_value)} };
static const lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0;
static lean_once_cell_t l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1;
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
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_instBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_ctor_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 46, 136, 228, 180, 199, 157, 185)}};
static const lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_bracketedBinder_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Term_bracketedBinder___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Term_bracketedBinder___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 328, .m_capacity = 328, .m_length = 323, .m_data = "A `bracketedBinder` matches any kind of binder group that uses some kind of brackets:\n* An explicit binder like `(x y : A)`\n* An implicit binder like `{x y : A}`\n* A strict implicit binder, `⦃y z : A⦄` or its ASCII alternative `{{y z : A}}`\n* An instance binder `[A]` or `[x : A]` (multiple variables are not allowed here)\n"};
static const lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 173, 248, 77, 70, 111, 216, 115)}};
static const lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Term_binderType_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_typeSpec_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_ctor_object l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 253, 28, 94, 107, 59, 142, 182)}};
static const lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 207, 90, 31, 52, 47, 237, 191)}};
static const lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_optEllipsis_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_ctor_object l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 107, 208, 253, 252, 167, 109, 165)}};
static const lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 232, 167, 67, 90, 227)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 119, 180, 184, 53, 176, 23, 24)}};
static const lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 232, 167, 67, 90, 227)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 252, 101, 22, 5, 156, 113, 37)}};
static const lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 11, 50, 166, 172, 142, 234, 224)}};
static const lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstLVal_formatter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 253, 40, 249, 57, 253, 160, 66)}};
static const lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 71, 141, 255, 254, 105, 125, 157)}};
static const lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Term_structInstField_formatter___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_ctor_object l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 10, 220, 108, 68, 147, 4, 252)}};
static const lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0 = (const lean_object*)&l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
v___x_182_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__3));
v___x_183_ = l_Lean_addBuiltinDocString(v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
v___x_238_ = ((lean_object*)(l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__2));
v___x_239_ = l_Lean_addBuiltinDocString(v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___y_281_; lean_object* v___x_291_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_));
v___x_276_ = ((lean_object*)(l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1___closed__2));
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
v___x_283_ = ((lean_object*)(l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1(){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_367_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___closed__0));
v___x_368_ = l_Lean_addBuiltinDocString(v___x_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1___boxed(lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_451_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_452_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___closed__1));
v___x_453_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_454_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_450_, v___x_451_, v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9(){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_492_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_493_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___closed__0));
v___x_494_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_495_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_491_, v___x_492_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9___boxed(lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13(){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_540_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_541_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___closed__0));
v___x_542_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_543_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_539_, v___x_540_, v___x_541_, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13___boxed(lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19(){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_614_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_615_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__1));
v___x_616_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___closed__1));
v___x_617_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_614_, v___x_615_, v___x_616_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19___boxed(lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23(){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_655_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_656_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq1Indented___closed__1));
v___x_657_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___closed__0));
v___x_658_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_659_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_655_, v___x_656_, v___x_657_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23___boxed(lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27(){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_697_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_698_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_699_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___closed__0));
v___x_700_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___x_701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_697_, v___x_698_, v___x_699_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27___boxed(lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1(){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_726_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___closed__0));
v___x_727_ = l_Lean_addBuiltinDocString(v___x_725_, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1___boxed(lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_formatter___boxed), 5, 0);
v___x_731_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_732_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_732_, 0, v___x_731_);
lean_closure_set(v___x_732_, 1, v___x_730_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__0);
v___x_734_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___boxed), 5, 0);
v___x_735_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_735_, 0, v___x_734_);
lean_closure_set(v___x_735_, 1, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__1);
v___x_737_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_738_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter___boxed), 7, 2);
lean_closure_set(v___x_738_, 0, v___x_737_);
lean_closure_set(v___x_738_, 1, v___x_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__2));
v___x_745_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2, &l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___closed__2);
v___x_746_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_744_, v___x_745_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter(v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3(){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_761_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_762_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_763_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___closed__1));
v___x_764_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed), 5, 0);
v___x_765_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_761_, v___x_762_, v___x_763_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3___boxed(lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
return v_res_767_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer___boxed), 5, 0);
v___x_769_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_770_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_770_, 0, v___x_769_);
lean_closure_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__0);
v___x_772_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___boxed), 5, 0);
v___x_773_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_773_, 0, v___x_772_);
lean_closure_set(v___x_773_, 1, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__1);
v___x_775_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_776_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_776_, 0, v___x_775_);
lean_closure_set(v___x_776_, 1, v___x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___closed__0));
v___x_783_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2, &l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___closed__2);
v___x_784_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_782_, v___x_783_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer(v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7(){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_798_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_799_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_800_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___closed__0));
v___x_801_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed), 5, 0);
v___x_802_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_798_, v___x_799_, v___x_800_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7___boxed(lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
return v_res_804_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__0));
v___x_807_ = l_Lean_Parser_checkColGt(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = l_Lean_Parser_Tactic_tacticSeq1Indented;
v___x_809_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__1);
v___x_810_ = l_Lean_Parser_andthen(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__2);
v___x_812_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_813_ = l_Lean_Parser_orelse(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__3);
v___x_815_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeq_formatter___closed__1));
v___x_816_ = l_Lean_Parser_node(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__4);
v___x_818_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq___closed__0, &l_Lean_Parser_Tactic_tacticSeq___closed__0_once, _init_l_Lean_Parser_Tactic_tacticSeq___closed__0);
v___x_819_ = l_Lean_Parser_withAntiquot(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tacticSeqIndentGt(void){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5, &l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5_once, _init_l_Lean_Parser_Tactic_tacticSeqIndentGt___closed__5);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1(){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__0));
v___x_829_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___closed__1));
v___x_830_ = l_Lean_addBuiltinDocString(v___x_828_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1___boxed(lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter(lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_854_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__4));
v___x_855_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_853_, v___x_854_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_formatter___boxed(lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Parser_Tactic_seq1_formatter(v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3(){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_869_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_870_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_871_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___closed__0));
v___x_872_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_formatter___boxed), 5, 0);
v___x_873_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_869_, v___x_870_, v___x_871_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3___boxed(lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer(lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_890_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_parenthesizer___closed__1));
v___x_891_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_889_, v___x_890_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1_parenthesizer___boxed(lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Parser_Tactic_seq1_parenthesizer(v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7(){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_905_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_906_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_907_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___closed__0));
v___x_908_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_seq1_parenthesizer___boxed), 5, 0);
v___x_909_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_905_, v___x_906_, v___x_907_, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7___boxed(lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
return v_res_911_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__0(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_913_ = l_Lean_Parser_symbol(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__1(void){
_start:
{
uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_914_ = 1;
v___x_915_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__0, &l_Lean_Parser_Tactic_seq1___closed__0_once, _init_l_Lean_Parser_Tactic_seq1___closed__0);
v___x_916_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__2));
v___x_917_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3, &l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3_once, _init_l_Lean_Parser_Tactic_tacticSeq1Indented___closed__3);
v___x_918_ = l_Lean_Parser_sepBy1(v___x_917_, v___x_916_, v___x_915_, v___x_914_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1___closed__2(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__1, &l_Lean_Parser_Tactic_seq1___closed__1_once, _init_l_Lean_Parser_Tactic_seq1___closed__1);
v___x_920_ = ((lean_object*)(l_Lean_Parser_Tactic_seq1_formatter___closed__1));
v___x_921_ = l_Lean_Parser_node(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_seq1(void){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_obj_once(&l_Lean_Parser_Tactic_seq1___closed__2, &l_Lean_Parser_Tactic_seq1___closed__2_once, _init_l_Lean_Parser_Tactic_seq1___closed__2);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__2(void){
_start:
{
uint8_t v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = 0;
v___x_930_ = 1;
v___x_931_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_932_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__0));
v___x_933_ = l_Lean_Parser_mkAntiquot(v___x_932_, v___x_931_, v___x_930_, v___x_929_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__4(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__3));
v___x_936_ = l_Lean_Parser_symbol(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__5(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_938_ = lean_unsigned_to_nat(1024u);
v___x_939_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_940_ = l_Lean_Parser_leadingNode(v___x_939_, v___x_938_, v___x_937_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__6(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__5, &l_Lean_Parser_Term_hole___closed__5_once, _init_l_Lean_Parser_Term_hole___closed__5);
v___x_942_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__2, &l_Lean_Parser_Term_hole___closed__2_once, _init_l_Lean_Parser_Term_hole___closed__2);
v___x_943_ = l_Lean_Parser_withAntiquot(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole___closed__7(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__6, &l_Lean_Parser_Term_hole___closed__6_once, _init_l_Lean_Parser_Term_hole___closed__6);
v___x_945_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_946_ = l_Lean_Parser_withCache(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Parser_Term_hole(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__7, &l_Lean_Parser_Term_hole___closed__7_once, _init_l_Lean_Parser_Term_hole___closed__7);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1(){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_952_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_953_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_954_ = l_Lean_Parser_Term_hole;
v___x_955_ = lean_unsigned_to_nat(1000u);
v___x_956_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_952_, v___x_953_, v___x_954_, v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___boxed(lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3(){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_962_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___closed__0));
v___x_963_ = l_Lean_addBuiltinDocString(v___x_961_, v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3___boxed(lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5(){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_993_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___closed__6));
v___x_994_ = l_Lean_addBuiltinDeclarationRanges(v___x_992_, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5___boxed(lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter(lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__0));
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Term_hole_formatter___closed__2));
v___x_1017_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1015_, v___x_1016_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Parser_Term_hole_formatter(v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9(){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1031_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1033_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___closed__0));
v___x_1034_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1035_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1031_, v___x_1032_, v___x_1033_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9___boxed(lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__0));
v___x_1057_ = ((lean_object*)(l_Lean_Parser_Term_hole_parenthesizer___closed__2));
v___x_1058_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1056_, v___x_1057_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Parser_Term_hole_parenthesizer(v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13(){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1072_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1073_ = ((lean_object*)(l_Lean_Parser_Term_hole___closed__1));
v___x_1074_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___closed__0));
v___x_1075_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1076_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1072_, v___x_1073_, v___x_1074_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13___boxed(lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
return v_res_1078_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__2(void){
_start:
{
uint8_t v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1085_ = 0;
v___x_1086_ = 1;
v___x_1087_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1088_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__0));
v___x_1089_ = l_Lean_Parser_mkAntiquot(v___x_1088_, v___x_1087_, v___x_1086_, v___x_1085_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__4(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__3));
v___x_1092_ = l_Lean_Parser_symbol(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__5(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_obj_once(&l_Lean_Parser_Term_hole___closed__4, &l_Lean_Parser_Term_hole___closed__4_once, _init_l_Lean_Parser_Term_hole___closed__4);
v___x_1094_ = l_Lean_Parser_ident;
v___x_1095_ = l_Lean_Parser_orelse(v___x_1094_, v___x_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__6(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__5, &l_Lean_Parser_Term_syntheticHole___closed__5_once, _init_l_Lean_Parser_Term_syntheticHole___closed__5);
v___x_1097_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__4, &l_Lean_Parser_Term_syntheticHole___closed__4_once, _init_l_Lean_Parser_Term_syntheticHole___closed__4);
v___x_1098_ = l_Lean_Parser_andthen(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__7(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__6, &l_Lean_Parser_Term_syntheticHole___closed__6_once, _init_l_Lean_Parser_Term_syntheticHole___closed__6);
v___x_1100_ = lean_unsigned_to_nat(1024u);
v___x_1101_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1102_ = l_Lean_Parser_leadingNode(v___x_1101_, v___x_1100_, v___x_1099_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__8(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__7, &l_Lean_Parser_Term_syntheticHole___closed__7_once, _init_l_Lean_Parser_Term_syntheticHole___closed__7);
v___x_1104_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__2, &l_Lean_Parser_Term_syntheticHole___closed__2_once, _init_l_Lean_Parser_Term_syntheticHole___closed__2);
v___x_1105_ = l_Lean_Parser_withAntiquot(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole___closed__9(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__8, &l_Lean_Parser_Term_syntheticHole___closed__8_once, _init_l_Lean_Parser_Term_syntheticHole___closed__8);
v___x_1107_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1108_ = l_Lean_Parser_withCache(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Parser_Term_syntheticHole(void){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Lean_Parser_Term_syntheticHole___closed__9, &l_Lean_Parser_Term_syntheticHole___closed__9_once, _init_l_Lean_Parser_Term_syntheticHole___closed__9);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1(){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1112_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1113_ = l_Lean_Parser_Term_syntheticHole;
v___x_1114_ = lean_unsigned_to_nat(1000u);
v___x_1115_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1111_, v___x_1112_, v___x_1113_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1___boxed(lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3(){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___closed__0));
v___x_1122_ = l_Lean_addBuiltinDocString(v___x_1120_, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3___boxed(lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5(){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1152_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___closed__6));
v___x_1153_ = l_Lean_addBuiltinDeclarationRanges(v___x_1151_, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5___boxed(lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter(lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__0));
v___x_1182_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__5));
v___x_1183_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1181_, v___x_1182_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_formatter___boxed(lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Parser_Term_syntheticHole_formatter(v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1197_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1198_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1199_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___closed__0));
v___x_1200_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_formatter___boxed), 5, 0);
v___x_1201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9___boxed(lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer(lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__0));
v___x_1230_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__5));
v___x_1231_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1229_, v___x_1230_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed(lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Parser_Term_syntheticHole_parenthesizer(v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13(){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1245_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1246_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___closed__1));
v___x_1247_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___closed__0));
v___x_1248_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed), 5, 0);
v___x_1249_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1245_, v___x_1246_, v___x_1247_, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13___boxed(lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
return v_res_1251_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__2(void){
_start:
{
uint8_t v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1258_ = 0;
v___x_1259_ = 1;
v___x_1260_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1261_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__0));
v___x_1262_ = l_Lean_Parser_mkAntiquot(v___x_1261_, v___x_1260_, v___x_1259_, v___x_1258_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__4(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__3));
v___x_1265_ = l_Lean_Parser_symbol(v___x_1264_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__5(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__4, &l_Lean_Parser_Term_omission___closed__4_once, _init_l_Lean_Parser_Term_omission___closed__4);
v___x_1267_ = lean_unsigned_to_nat(1024u);
v___x_1268_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1269_ = l_Lean_Parser_leadingNode(v___x_1268_, v___x_1267_, v___x_1266_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__6(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__5, &l_Lean_Parser_Term_omission___closed__5_once, _init_l_Lean_Parser_Term_omission___closed__5);
v___x_1271_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__2, &l_Lean_Parser_Term_omission___closed__2_once, _init_l_Lean_Parser_Term_omission___closed__2);
v___x_1272_ = l_Lean_Parser_withAntiquot(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission___closed__7(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__6, &l_Lean_Parser_Term_omission___closed__6_once, _init_l_Lean_Parser_Term_omission___closed__6);
v___x_1274_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1275_ = l_Lean_Parser_withCache(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_Parser_Term_omission(void){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_obj_once(&l_Lean_Parser_Term_omission___closed__7, &l_Lean_Parser_Term_omission___closed__7_once, _init_l_Lean_Parser_Term_omission___closed__7);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1(){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1278_ = ((lean_object*)(l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1___closed__1));
v___x_1279_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1280_ = l_Lean_Parser_Term_omission;
v___x_1281_ = lean_unsigned_to_nat(1000u);
v___x_1282_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1278_, v___x_1279_, v___x_1280_, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1___boxed(lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3(){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1288_ = ((lean_object*)(l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___closed__0));
v___x_1289_ = l_Lean_addBuiltinDocString(v___x_1287_, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3___boxed(lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5(){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1319_ = ((lean_object*)(l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___closed__6));
v___x_1320_ = l_Lean_addBuiltinDeclarationRanges(v___x_1318_, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5___boxed(lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter(lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__0));
v___x_1342_ = ((lean_object*)(l_Lean_Parser_Term_omission_formatter___closed__2));
v___x_1343_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1341_, v___x_1342_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_formatter___boxed(lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Parser_Term_omission_formatter(v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9(){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1357_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1358_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1359_ = ((lean_object*)(l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___closed__0));
v___x_1360_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_formatter___boxed), 5, 0);
v___x_1361_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1357_, v___x_1358_, v___x_1359_, v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9___boxed(lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer(lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__0));
v___x_1383_ = ((lean_object*)(l_Lean_Parser_Term_omission_parenthesizer___closed__2));
v___x_1384_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1382_, v___x_1383_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission_parenthesizer___boxed(lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Parser_Term_omission_parenthesizer(v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13(){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1399_ = ((lean_object*)(l_Lean_Parser_Term_omission___closed__1));
v___x_1400_ = ((lean_object*)(l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___closed__0));
v___x_1401_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_omission_parenthesizer___boxed), 5, 0);
v___x_1402_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1398_, v___x_1399_, v___x_1400_, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13___boxed(lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_1411_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_formatter___boxed), 5, 0);
v___x_1412_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1410_, v___x_1411_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_formatter___boxed(lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Parser_Term_binderIdent_formatter(v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_1425_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_hole_parenthesizer___boxed), 5, 0);
v___x_1426_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_1424_, v___x_1425_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer___boxed(lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Parser_Term_binderIdent_parenthesizer(v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
return v_res_1432_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent___closed__0(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = l_Lean_Parser_Term_hole;
v___x_1434_ = l_Lean_Parser_ident;
v___x_1435_ = l_Lean_Parser_orelse(v___x_1434_, v___x_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderIdent(void){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_obj_once(&l_Lean_Parser_Term_binderIdent___closed__0, &l_Lean_Parser_Term_binderIdent___closed__0_once, _init_l_Lean_Parser_Term_binderIdent___closed__0);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter(uint8_t v_requireType_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
if (v_requireType_1448_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1455_ = l_Lean_Parser_optional_formatter(v___x_1454_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1457_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__3));
v___x_1458_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_1456_, v___x_1457_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_formatter___boxed(lean_object* v_requireType_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_requireType_boxed_1465_; lean_object* v_res_1466_; 
v_requireType_boxed_1465_ = lean_unbox(v_requireType_1459_);
v_res_1466_ = l_Lean_Parser_Term_binderType_formatter(v_requireType_boxed_1465_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer(uint8_t v_requireType_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
if (v_requireType_1474_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1481_ = l_Lean_Parser_optional_parenthesizer(v___x_1480_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1483_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__2));
v___x_1484_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_1482_, v___x_1483_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType_parenthesizer___boxed(lean_object* v_requireType_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
uint8_t v_requireType_boxed_1491_; lean_object* v_res_1492_; 
v_requireType_boxed_1491_ = lean_unbox(v_requireType_1485_);
v_res_1492_ = l_Lean_Parser_Term_binderType_parenthesizer(v_requireType_boxed_1491_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1492_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__0));
v___x_1494_ = l_Lean_Parser_symbol(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__1(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l_Lean_Parser_termParser(v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__2(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1498_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1499_ = l_Lean_Parser_andthen(v___x_1498_, v___x_1497_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__3(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1501_ = l_Lean_Parser_optional(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderType___closed__4(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_1503_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__5));
v___x_1504_ = l_Lean_Parser_node(v___x_1503_, v___x_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType(uint8_t v_requireType_1505_){
_start:
{
if (v_requireType_1505_ == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__3, &l_Lean_Parser_Term_binderType___closed__3_once, _init_l_Lean_Parser_Term_binderType___closed__3);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__4, &l_Lean_Parser_Term_binderType___closed__4_once, _init_l_Lean_Parser_Term_binderType___closed__4);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderType___boxed(lean_object* v_requireType_1508_){
_start:
{
uint8_t v_requireType_boxed_1509_; lean_object* v_res_1510_; 
v_requireType_boxed_1509_ = lean_unbox(v_requireType_1508_);
v_res_1510_ = l_Lean_Parser_Term_binderType(v_requireType_boxed_1509_);
return v_res_1510_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_formatter___boxed), 5, 0);
v___x_1536_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__8));
v___x_1537_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1537_, 0, v___x_1536_);
lean_closure_set(v___x_1537_, 1, v___x_1535_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__9, &l_Lean_Parser_Term_binderTactic_formatter___closed__9_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__9);
v___x_1539_ = lean_unsigned_to_nat(1024u);
v___x_1540_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1541_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1541_, 0, v___x_1540_);
lean_closure_set(v___x_1541_, 1, v___x_1539_);
lean_closure_set(v___x_1541_, 2, v___x_1538_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter(lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__2));
v___x_1548_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_formatter___closed__10, &l_Lean_Parser_Term_binderTactic_formatter___closed__10_once, _init_l_Lean_Parser_Term_binderTactic_formatter___closed__10);
v___x_1549_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1547_, v___x_1548_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_formatter___boxed(lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Parser_Term_binderTactic_formatter(v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3(){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1563_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1564_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1565_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___closed__0));
v___x_1566_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_1567_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1563_, v___x_1564_, v___x_1565_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3___boxed(lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_1570_, v___x_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed(lean_object* v___x_1578_, lean_object* v___x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0(v___x_1578_, v___x_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed), 5, 0);
v___f_1601_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__3));
v___x_1602_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1602_, 0, v___f_1601_);
lean_closure_set(v___x_1602_, 1, v___x_1600_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__4);
v___x_1604_ = lean_unsigned_to_nat(1024u);
v___x_1605_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1606_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1606_, 0, v___x_1605_);
lean_closure_set(v___x_1606_, 1, v___x_1604_);
lean_closure_set(v___x_1606_, 2, v___x_1603_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer(lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_parenthesizer___closed__0));
v___x_1613_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5, &l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_binderTactic_parenthesizer___closed__5);
v___x_1614_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1612_, v___x_1613_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic_parenthesizer___boxed(lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Parser_Term_binderTactic_parenthesizer(v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7(){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1628_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1629_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1630_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___closed__0));
v___x_1631_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_1632_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1628_, v___x_1629_, v___x_1630_, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7___boxed(lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
return v_res_1634_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__0(void){
_start:
{
uint8_t v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1635_ = 0;
v___x_1636_ = 1;
v___x_1637_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1638_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__0));
v___x_1639_ = l_Lean_Parser_mkAntiquot(v___x_1638_, v___x_1637_, v___x_1636_, v___x_1635_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__1(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__3));
v___x_1641_ = l_Lean_Parser_symbol(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__2(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__5));
v___x_1643_ = l_Lean_Parser_symbol(v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__3(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__2, &l_Lean_Parser_Term_binderTactic___closed__2_once, _init_l_Lean_Parser_Term_binderTactic___closed__2);
v___x_1645_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1646_ = l_Lean_Parser_andthen(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__4(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__3, &l_Lean_Parser_Term_binderTactic___closed__3_once, _init_l_Lean_Parser_Term_binderTactic___closed__3);
v___x_1648_ = l_Lean_Parser_atomic(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__5(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_1650_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__4, &l_Lean_Parser_Term_binderTactic___closed__4_once, _init_l_Lean_Parser_Term_binderTactic___closed__4);
v___x_1651_ = l_Lean_Parser_andthen(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__6(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__5, &l_Lean_Parser_Term_binderTactic___closed__5_once, _init_l_Lean_Parser_Term_binderTactic___closed__5);
v___x_1653_ = lean_unsigned_to_nat(1024u);
v___x_1654_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1655_ = l_Lean_Parser_leadingNode(v___x_1654_, v___x_1653_, v___x_1652_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__7(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__6, &l_Lean_Parser_Term_binderTactic___closed__6_once, _init_l_Lean_Parser_Term_binderTactic___closed__6);
v___x_1657_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__0, &l_Lean_Parser_Term_binderTactic___closed__0_once, _init_l_Lean_Parser_Term_binderTactic___closed__0);
v___x_1658_ = l_Lean_Parser_withAntiquot(v___x_1657_, v___x_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic___closed__8(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__7, &l_Lean_Parser_Term_binderTactic___closed__7_once, _init_l_Lean_Parser_Term_binderTactic___closed__7);
v___x_1660_ = ((lean_object*)(l_Lean_Parser_Term_binderTactic_formatter___closed__1));
v___x_1661_ = l_Lean_Parser_withCache(v___x_1660_, v___x_1659_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderTactic(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__8, &l_Lean_Parser_Term_binderTactic___closed__8_once, _init_l_Lean_Parser_Term_binderTactic___closed__8);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__2(void){
_start:
{
uint8_t v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = 0;
v___x_1670_ = 1;
v___x_1671_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1672_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__0));
v___x_1673_ = l_Lean_Parser_mkAntiquot(v___x_1672_, v___x_1671_, v___x_1670_, v___x_1669_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1675_ = lean_obj_once(&l_Lean_Parser_Term_binderTactic___closed__1, &l_Lean_Parser_Term_binderTactic___closed__1_once, _init_l_Lean_Parser_Term_binderTactic___closed__1);
v___x_1676_ = l_Lean_Parser_andthen(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__4(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__3, &l_Lean_Parser_Term_binderDefault___closed__3_once, _init_l_Lean_Parser_Term_binderDefault___closed__3);
v___x_1678_ = lean_unsigned_to_nat(1024u);
v___x_1679_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1680_ = l_Lean_Parser_leadingNode(v___x_1679_, v___x_1678_, v___x_1677_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__5(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__4, &l_Lean_Parser_Term_binderDefault___closed__4_once, _init_l_Lean_Parser_Term_binderDefault___closed__4);
v___x_1682_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__2, &l_Lean_Parser_Term_binderDefault___closed__2_once, _init_l_Lean_Parser_Term_binderDefault___closed__2);
v___x_1683_ = l_Lean_Parser_withAntiquot(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault___closed__6(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__5, &l_Lean_Parser_Term_binderDefault___closed__5_once, _init_l_Lean_Parser_Term_binderDefault___closed__5);
v___x_1685_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_1686_ = l_Lean_Parser_withCache(v___x_1685_, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_Parser_Term_binderDefault(void){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_obj_once(&l_Lean_Parser_Term_binderDefault___closed__6, &l_Lean_Parser_Term_binderDefault___closed__6_once, _init_l_Lean_Parser_Term_binderDefault___closed__6);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_binderDefaultM(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Parser_Term_binderDefault;
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v_stxTrav_1692_; lean_object* v_cur_1693_; lean_object* v___x_1694_; 
v___x_1691_ = lean_st_ref_get(v___y_1689_);
v_stxTrav_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc_ref(v_stxTrav_1692_);
lean_dec(v___x_1691_);
v_cur_1693_ = lean_ctor_get(v_stxTrav_1692_, 0);
lean_inc(v_cur_1693_);
lean_dec_ref(v_stxTrav_1692_);
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_cur_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg___boxed(lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1695_);
lean_dec(v___y_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v___y_1699_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___boxed(lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0(v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1716_);
v___x_1717_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_1712_);
return v___x_1717_;
}
else
{
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed(lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0(v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer(lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v_a_1737_; lean_object* v___y_1739_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1736_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Parser_Term_binderDefault_parenthesizer_spec__0___redArg(v_a_1732_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1742_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
lean_inc(v_a_1737_);
v___x_1743_ = l_Lean_Syntax_isOfKind(v_a_1737_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec(v_a_1737_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___y_1739_ = v___x_1744_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = l_Lean_Syntax_getArg(v_a_1737_, v___x_1745_);
lean_dec(v_a_1737_);
v___x_1747_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_parenthesizer___closed__1));
v___x_1748_ = l_Lean_Syntax_isOfKind(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v___y_1739_ = v___x_1749_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Parser_maxPrec;
v___y_1739_ = v___x_1750_;
goto v___jp_1738_;
}
}
v___jp_1738_:
{
lean_object* v___f_1740_; lean_object* v___x_1741_; 
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1740_, 0, v___y_1739_);
v___x_1741_ = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(v___f_1740_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_parenthesizer___boxed(lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Parser_Term_binderDefault_parenthesizer(v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1756_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1763_ = 0;
v___x_1764_ = 1;
v___x_1765_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1766_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__0));
v___x_1767_ = l_Lean_Parser_mkAntiquot(v___x_1766_, v___x_1765_, v___x_1764_, v___x_1763_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__3));
v___x_1770_ = l_Lean_Parser_symbol(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__5(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = l_Lean_Parser_Term_binderIdent;
v___x_1772_ = l_Lean_Parser_many1(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__6(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = l_Lean_Parser_Term_binderDefault;
v___x_1774_ = l_Lean_Parser_Term_binderTactic;
v___x_1775_ = l_Lean_Parser_orelse(v___x_1774_, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__7(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__6, &l_Lean_Parser_Term_explicitBinder___closed__6_once, _init_l_Lean_Parser_Term_explicitBinder___closed__6);
v___x_1777_ = l_Lean_Parser_optional(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder___closed__9(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__8));
v___x_1780_ = l_Lean_Parser_symbol(v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder(uint8_t v_requireType_1781_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1782_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1783_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__2, &l_Lean_Parser_Term_explicitBinder___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder___closed__2);
v___x_1784_ = lean_unsigned_to_nat(1024u);
v___x_1785_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__4, &l_Lean_Parser_Term_explicitBinder___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder___closed__4);
v___x_1786_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1787_ = l_Lean_Parser_Term_binderType(v_requireType_1781_);
v___x_1788_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__7, &l_Lean_Parser_Term_explicitBinder___closed__7_once, _init_l_Lean_Parser_Term_explicitBinder___closed__7);
v___x_1789_ = l_Lean_Parser_andthen(v___x_1787_, v___x_1788_);
v___x_1790_ = l_Lean_Parser_andthen(v___x_1786_, v___x_1789_);
v___x_1791_ = l_Lean_Parser_withoutPosition(v___x_1790_);
v___x_1792_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__9, &l_Lean_Parser_Term_explicitBinder___closed__9_once, _init_l_Lean_Parser_Term_explicitBinder___closed__9);
v___x_1793_ = l_Lean_Parser_andthen(v___x_1791_, v___x_1792_);
v___x_1794_ = l_Lean_Parser_andthen(v___x_1785_, v___x_1793_);
v___x_1795_ = l_Lean_Parser_leadingNode(v___x_1782_, v___x_1784_, v___x_1794_);
v___x_1796_ = l_Lean_Parser_withAntiquot(v___x_1783_, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___boxed(lean_object* v_requireType_1797_){
_start:
{
uint8_t v_requireType_boxed_1798_; lean_object* v_res_1799_; 
v_requireType_boxed_1798_ = lean_unbox(v_requireType_1797_);
v_res_1799_ = l_Lean_Parser_Term_explicitBinder(v_requireType_boxed_1798_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1(){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_1803_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___closed__0));
v___x_1804_ = l_Lean_addBuiltinDocString(v___x_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1___boxed(lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1813_ = 0;
v___x_1814_ = 1;
v___x_1815_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1816_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__0));
v___x_1817_ = l_Lean_Parser_mkAntiquot(v___x_1816_, v___x_1815_, v___x_1814_, v___x_1813_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_Parser_Term_implicitBinder___closed__4(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__3));
v___x_1820_ = l_Lean_Parser_symbol(v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder(uint8_t v_requireType_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1822_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1823_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__2, &l_Lean_Parser_Term_implicitBinder___closed__2_once, _init_l_Lean_Parser_Term_implicitBinder___closed__2);
v___x_1824_ = lean_unsigned_to_nat(1024u);
v___x_1825_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1826_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1827_ = l_Lean_Parser_Term_binderType(v_requireType_1821_);
v___x_1828_ = l_Lean_Parser_andthen(v___x_1826_, v___x_1827_);
v___x_1829_ = l_Lean_Parser_withoutPosition(v___x_1828_);
v___x_1830_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1831_ = l_Lean_Parser_andthen(v___x_1829_, v___x_1830_);
v___x_1832_ = l_Lean_Parser_andthen(v___x_1825_, v___x_1831_);
v___x_1833_ = l_Lean_Parser_leadingNode(v___x_1822_, v___x_1824_, v___x_1832_);
v___x_1834_ = l_Lean_Parser_withAntiquot(v___x_1823_, v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___boxed(lean_object* v_requireType_1835_){
_start:
{
uint8_t v_requireType_boxed_1836_; lean_object* v_res_1837_; 
v_requireType_boxed_1836_ = lean_unbox(v_requireType_1835_);
v_res_1837_ = l_Lean_Parser_Term_implicitBinder(v_requireType_boxed_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1(){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_1841_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___closed__0));
v___x_1842_ = l_Lean_addBuiltinDocString(v___x_1840_, v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1___boxed(lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_obj_once(&l_Lean_Parser_Term_implicitBinder___closed__4, &l_Lean_Parser_Term_implicitBinder___closed__4_once, _init_l_Lean_Parser_Term_implicitBinder___closed__4);
v___x_1846_ = l_Lean_Parser_andthen(v___x_1845_, v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__0);
v___x_1851_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1852_ = l_Lean_Parser_node(v___x_1851_, v___x_1850_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__3);
v___x_1854_ = l_Lean_Parser_atomic(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__5));
v___x_1857_ = l_Lean_Parser_symbol(v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__6);
v___x_1859_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__4);
v___x_1860_ = l_Lean_Parser_orelse(v___x_1859_, v___x_1858_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket(void){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7, &l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket___closed__7);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_1863_ = l_Lean_Parser_andthen(v___x_1862_, v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__0, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__0);
v___x_1865_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_1866_ = l_Lean_Parser_node(v___x_1865_, v___x_1864_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__1, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__1);
v___x_1868_ = l_Lean_Parser_atomic(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket___closed__3));
v___x_1871_ = l_Lean_Parser_symbol(v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__4, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__4_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__4);
v___x_1873_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__2, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__2);
v___x_1874_ = l_Lean_Parser_orelse(v___x_1873_, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket___closed__5, &l_Lean_Parser_Term_strictImplicitRightBracket___closed__5_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket___closed__5);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2(void){
_start:
{
uint8_t v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1882_ = 0;
v___x_1883_ = 1;
v___x_1884_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1885_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__0));
v___x_1886_ = l_Lean_Parser_mkAntiquot(v___x_1885_, v___x_1884_, v___x_1883_, v___x_1882_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder(uint8_t v_requireType_1887_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1888_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1889_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitBinder___closed__2, &l_Lean_Parser_Term_strictImplicitBinder___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitBinder___closed__2);
v___x_1890_ = lean_unsigned_to_nat(1024u);
v___x_1891_ = l_Lean_Parser_Term_strictImplicitLeftBracket;
v___x_1892_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder___closed__5, &l_Lean_Parser_Term_explicitBinder___closed__5_once, _init_l_Lean_Parser_Term_explicitBinder___closed__5);
v___x_1893_ = l_Lean_Parser_Term_binderType(v_requireType_1887_);
v___x_1894_ = l_Lean_Parser_Term_strictImplicitRightBracket;
v___x_1895_ = l_Lean_Parser_andthen(v___x_1893_, v___x_1894_);
v___x_1896_ = l_Lean_Parser_andthen(v___x_1892_, v___x_1895_);
v___x_1897_ = l_Lean_Parser_andthen(v___x_1891_, v___x_1896_);
v___x_1898_ = l_Lean_Parser_leadingNode(v___x_1888_, v___x_1890_, v___x_1897_);
v___x_1899_ = l_Lean_Parser_withAntiquot(v___x_1889_, v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___boxed(lean_object* v_requireType_1900_){
_start:
{
uint8_t v_requireType_boxed_1901_; lean_object* v_res_1902_; 
v_requireType_boxed_1901_ = lean_unbox(v_requireType_1900_);
v_res_1902_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_boxed_1901_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1(){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_1906_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___closed__0));
v___x_1907_ = l_Lean_addBuiltinDocString(v___x_1905_, v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1___boxed(lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
return v_res_1909_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__0(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__0, &l_Lean_Parser_Term_binderType___closed__0_once, _init_l_Lean_Parser_Term_binderType___closed__0);
v___x_1911_ = l_Lean_Parser_ident;
v___x_1912_ = l_Lean_Parser_andthen(v___x_1911_, v___x_1910_);
return v___x_1912_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__1(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__0, &l_Lean_Parser_Term_optIdent___closed__0_once, _init_l_Lean_Parser_Term_optIdent___closed__0);
v___x_1914_ = l_Lean_Parser_atomic(v___x_1913_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent___closed__2(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__1, &l_Lean_Parser_Term_optIdent___closed__1_once, _init_l_Lean_Parser_Term_optIdent___closed__1);
v___x_1916_ = l_Lean_Parser_optional(v___x_1915_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optIdent(void){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_obj_once(&l_Lean_Parser_Term_optIdent___closed__2, &l_Lean_Parser_Term_optIdent___closed__2_once, _init_l_Lean_Parser_Term_optIdent___closed__2);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__2(void){
_start:
{
uint8_t v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1924_ = 0;
v___x_1925_ = 1;
v___x_1926_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1927_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__0));
v___x_1928_ = l_Lean_Parser_mkAntiquot(v___x_1927_, v___x_1926_, v___x_1925_, v___x_1924_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__4(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__3));
v___x_1931_ = l_Lean_Parser_symbol(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__5(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_1933_ = l_Lean_Parser_Term_optIdent;
v___x_1934_ = l_Lean_Parser_andthen(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__6(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__5, &l_Lean_Parser_Term_instBinder___closed__5_once, _init_l_Lean_Parser_Term_instBinder___closed__5);
v___x_1936_ = l_Lean_Parser_withoutPosition(v___x_1935_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__8(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__7));
v___x_1939_ = l_Lean_Parser_symbol(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__9(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_1941_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__6, &l_Lean_Parser_Term_instBinder___closed__6_once, _init_l_Lean_Parser_Term_instBinder___closed__6);
v___x_1942_ = l_Lean_Parser_andthen(v___x_1941_, v___x_1940_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__10(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__9, &l_Lean_Parser_Term_instBinder___closed__9_once, _init_l_Lean_Parser_Term_instBinder___closed__9);
v___x_1944_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_1945_ = l_Lean_Parser_andthen(v___x_1944_, v___x_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__11(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__10, &l_Lean_Parser_Term_instBinder___closed__10_once, _init_l_Lean_Parser_Term_instBinder___closed__10);
v___x_1947_ = lean_unsigned_to_nat(1024u);
v___x_1948_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1949_ = l_Lean_Parser_leadingNode(v___x_1948_, v___x_1947_, v___x_1946_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__12(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__11, &l_Lean_Parser_Term_instBinder___closed__11_once, _init_l_Lean_Parser_Term_instBinder___closed__11);
v___x_1951_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__2, &l_Lean_Parser_Term_instBinder___closed__2_once, _init_l_Lean_Parser_Term_instBinder___closed__2);
v___x_1952_ = l_Lean_Parser_withAntiquot(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder___closed__13(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__12, &l_Lean_Parser_Term_instBinder___closed__12_once, _init_l_Lean_Parser_Term_instBinder___closed__12);
v___x_1954_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1955_ = l_Lean_Parser_withCache(v___x_1954_, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder(void){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__13, &l_Lean_Parser_Term_instBinder___closed__13_once, _init_l_Lean_Parser_Term_instBinder___closed__13);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1(){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_1960_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___closed__0));
v___x_1961_ = l_Lean_addBuiltinDocString(v___x_1959_, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1___boxed(lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter(lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__0));
v___x_1984_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault_formatter___closed__2));
v___x_1985_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1983_, v___x_1984_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_binderDefault_formatter___boxed(lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_Parser_Term_binderDefault_formatter(v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3(){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_1999_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2000_ = ((lean_object*)(l_Lean_Parser_Term_binderDefault___closed__1));
v___x_2001_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___closed__0));
v___x_2002_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2003_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1999_, v___x_2000_, v___x_2001_, v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3___boxed(lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
return v_res_2005_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_2016_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter___boxed), 6, 1);
lean_closure_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_formatter___boxed), 5, 0);
v___x_2018_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_formatter___boxed), 5, 0);
v___x_2019_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2019_, 0, v___x_2018_);
lean_closure_set(v___x_2019_, 1, v___x_2017_);
return v___x_2019_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__3, &l_Lean_Parser_Term_explicitBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__3);
v___x_2021_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter(uint8_t v_requireType_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2030_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2031_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__0));
v___x_2032_ = lean_unsigned_to_nat(1024u);
v___x_2033_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__1));
v___x_2034_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2035_ = lean_box(v_requireType_2024_);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__4, &l_Lean_Parser_Term_explicitBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__4);
v___x_2038_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2038_, 0, v___x_2036_);
lean_closure_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2039_, 0, v___x_2034_);
lean_closure_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2040_, 0, v___x_2039_);
v___x_2041_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_formatter___closed__5));
v___x_2042_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2042_, 0, v___x_2040_);
lean_closure_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2043_, 0, v___x_2033_);
lean_closure_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2044_, 0, v___x_2043_);
v___x_2045_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2045_, 0, v___x_2030_);
lean_closure_set(v___x_2045_, 1, v___x_2032_);
lean_closure_set(v___x_2045_, 2, v___x_2044_);
v___x_2046_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2031_, v___x_2045_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_formatter___boxed(lean_object* v_requireType_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v_requireType_boxed_2053_; lean_object* v_res_2054_; 
v_requireType_boxed_2053_ = lean_unbox(v_requireType_2047_);
v_res_2054_ = l_Lean_Parser_Term_explicitBinder_formatter(v_requireType_boxed_2053_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2054_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0));
v___x_2058_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2058_, 0, v___x_2057_);
lean_closure_set(v___x_2058_, 1, v___x_2057_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1, &l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__1);
v___x_2060_ = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter___boxed), 6, 1);
lean_closure_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2, &l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__2);
v___x_2062_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3, &l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__3);
v___x_2071_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__4));
v___x_2072_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2070_, v___x_2071_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed(lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Parser_Term_strictImplicitLeftBracket_formatter(v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
return v_res_2078_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_2080_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2080_, 0, v___x_2079_);
lean_closure_set(v___x_2080_, 1, v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0, &l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__0);
v___x_2082_ = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter___boxed), 6, 1);
lean_closure_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1, &l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__1);
v___x_2084_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter(lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2, &l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__2);
v___x_2093_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___closed__3));
v___x_2094_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2092_, v___x_2093_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed(lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Parser_Term_strictImplicitRightBracket_formatter(v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter(uint8_t v_requireType_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2114_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2115_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___closed__0));
v___x_2116_ = lean_unsigned_to_nat(1024u);
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___boxed), 5, 0);
v___x_2118_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2119_ = lean_box(v_requireType_2108_);
v___x_2120_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2120_, 0, v___x_2119_);
v___x_2121_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_formatter___boxed), 5, 0);
v___x_2122_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2122_, 0, v___x_2120_);
lean_closure_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2123_, 0, v___x_2118_);
lean_closure_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2124_, 0, v___x_2117_);
lean_closure_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2125_, 0, v___x_2124_);
v___x_2126_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2126_, 0, v___x_2114_);
lean_closure_set(v___x_2126_, 1, v___x_2116_);
lean_closure_set(v___x_2126_, 2, v___x_2125_);
v___x_2127_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2115_, v___x_2126_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed(lean_object* v_requireType_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
uint8_t v_requireType_boxed_2134_; lean_object* v_res_2135_; 
v_requireType_boxed_2134_ = lean_unbox(v_requireType_2128_);
v_res_2135_ = l_Lean_Parser_Term_strictImplicitBinder_formatter(v_requireType_boxed_2134_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter(uint8_t v_requireType_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2149_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2150_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_formatter___closed__0));
v___x_2151_ = lean_unsigned_to_nat(1024u);
v___x_2152_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_formatter___closed__0));
v___x_2153_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_formatter___closed__2, &l_Lean_Parser_Term_explicitBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_formatter___closed__2);
v___x_2154_ = lean_box(v_requireType_2143_);
v___x_2155_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_formatter___boxed), 6, 1);
lean_closure_set(v___x_2155_, 0, v___x_2154_);
v___x_2156_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2156_, 0, v___x_2153_);
lean_closure_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2157_, 0, v___x_2156_);
v___x_2158_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_formatter___closed__5));
v___x_2159_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2159_, 0, v___x_2157_);
lean_closure_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2160_, 0, v___x_2152_);
lean_closure_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2162_, 0, v___x_2149_);
lean_closure_set(v___x_2162_, 1, v___x_2151_);
lean_closure_set(v___x_2162_, 2, v___x_2161_);
v___x_2163_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2150_, v___x_2162_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_formatter___boxed(lean_object* v_requireType_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
uint8_t v_requireType_boxed_2170_; lean_object* v_res_2171_; 
v_requireType_boxed_2170_ = lean_unbox(v_requireType_2164_);
v_res_2171_ = l_Lean_Parser_Term_implicitBinder_formatter(v_requireType_boxed_2170_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter(lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_formatter___closed__1));
v___x_2183_ = l_Lean_Parser_optional_formatter(v___x_2182_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_formatter___boxed(lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Parser_Term_optIdent_formatter(v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
return v_res_2189_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__2(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((lean_object*)(l_Lean_Parser_Term_binderType_formatter___closed__2));
v___x_2200_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_formatter___boxed), 5, 0);
v___x_2201_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2201_, 0, v___x_2200_);
lean_closure_set(v___x_2201_, 1, v___x_2199_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__3(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__2, &l_Lean_Parser_Term_instBinder_formatter___closed__2_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__2);
v___x_2203_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter___boxed), 6, 1);
lean_closure_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__5(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__4));
v___x_2207_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__3, &l_Lean_Parser_Term_instBinder_formatter___closed__3_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__3);
v___x_2208_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2208_, 0, v___x_2207_);
lean_closure_set(v___x_2208_, 1, v___x_2206_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__6(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__5, &l_Lean_Parser_Term_instBinder_formatter___closed__5_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__5);
v___x_2210_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__1));
v___x_2211_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2211_, 0, v___x_2210_);
lean_closure_set(v___x_2211_, 1, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__7(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__6, &l_Lean_Parser_Term_instBinder_formatter___closed__6_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__6);
v___x_2213_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter___boxed), 6, 1);
lean_closure_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_formatter___closed__8(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__7, &l_Lean_Parser_Term_instBinder_formatter___closed__7_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__7);
v___x_2215_ = lean_unsigned_to_nat(1024u);
v___x_2216_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2217_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_2217_, 0, v___x_2216_);
lean_closure_set(v___x_2217_, 1, v___x_2215_);
lean_closure_set(v___x_2217_, 2, v___x_2214_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter(lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_formatter___closed__0));
v___x_2224_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_formatter___closed__8, &l_Lean_Parser_Term_instBinder_formatter___closed__8_once, _init_l_Lean_Parser_Term_instBinder_formatter___closed__8);
v___x_2225_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2223_, v___x_2224_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_formatter___boxed(lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Parser_Term_instBinder_formatter(v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19(){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2239_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2240_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2241_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___closed__0));
v___x_2242_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2243_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2239_, v___x_2240_, v___x_2241_, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19___boxed(lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter(uint8_t v_requireType_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2264_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__2));
v___x_2265_ = lean_box(v_requireType_2258_);
v___x_2266_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = lean_box(v_requireType_2258_);
v___x_2268_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_box(v_requireType_2258_);
v___x_2270_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_formatter___boxed), 6, 1);
lean_closure_set(v___x_2270_, 0, v___x_2269_);
v___x_2271_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_formatter___boxed), 5, 0);
v___x_2272_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2272_, 0, v___x_2270_);
lean_closure_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2273_, 0, v___x_2268_);
lean_closure_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2274_, 0, v___x_2266_);
lean_closure_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2264_, v___x_2274_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object* v_requireType_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
uint8_t v_requireType_boxed_2282_; lean_object* v_res_2283_; 
v_requireType_boxed_2282_ = lean_unbox(v_requireType_2276_);
v_res_2283_ = l_Lean_Parser_Term_bracketedBinder_formatter(v_requireType_boxed_2282_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
return v_res_2283_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_2294_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderDefault_parenthesizer___boxed), 5, 0);
v___x_2296_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___boxed), 5, 0);
v___x_2297_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2297_, 0, v___x_2296_);
lean_closure_set(v___x_2297_, 1, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__3);
v___x_2299_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer(uint8_t v_requireType_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2308_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder___closed__1));
v___x_2309_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__0));
v___x_2310_ = lean_unsigned_to_nat(1024u);
v___x_2311_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__1));
v___x_2312_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2313_ = lean_box(v_requireType_2302_);
v___x_2314_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2314_, 0, v___x_2313_);
v___x_2315_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__4);
v___x_2316_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2316_, 0, v___x_2314_);
lean_closure_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2317_, 0, v___x_2312_);
lean_closure_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2318_, 0, v___x_2317_);
v___x_2319_ = ((lean_object*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__5));
v___x_2320_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2320_, 0, v___x_2318_);
lean_closure_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2321_, 0, v___x_2311_);
lean_closure_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2322_, 0, v___x_2321_);
v___x_2323_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2323_, 0, v___x_2308_);
lean_closure_set(v___x_2323_, 1, v___x_2310_);
lean_closure_set(v___x_2323_, 2, v___x_2322_);
v___x_2324_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2309_, v___x_2323_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed(lean_object* v_requireType_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
uint8_t v_requireType_boxed_2331_; lean_object* v_res_2332_; 
v_requireType_boxed_2331_ = lean_unbox(v_requireType_2325_);
v_res_2332_ = l_Lean_Parser_Term_explicitBinder_parenthesizer(v_requireType_boxed_2331_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(lean_object* v___x_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Parser_group_parenthesizer(v___x_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed(lean_object* v___x_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0(v___x_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2346_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0));
v___x_2350_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2350_, 0, v___x_2349_);
lean_closure_set(v___x_2350_, 1, v___x_2349_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___f_2352_; 
v___x_2351_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1, &l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__1);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2352_, 0, v___x_2351_);
return v___f_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___f_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___f_2360_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2, &l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__2);
v___x_2361_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__3));
v___x_2362_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2360_, v___x_2361_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed(lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer(v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2368_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6));
v___x_2370_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2370_, 0, v___x_2369_);
lean_closure_set(v___x_2370_, 1, v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___f_2372_; 
v___x_2371_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0, &l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__0);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2372_, 0, v___x_2371_);
return v___f_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___f_2380_ = lean_obj_once(&l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1, &l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1_once, _init_l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__1);
v___x_2381_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___closed__2));
v___x_2382_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___f_2380_, v___x_2381_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed(lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer(v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(uint8_t v_requireType_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2402_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder___closed__1));
v___x_2403_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___closed__0));
v___x_2404_ = lean_unsigned_to_nat(1024u);
v___x_2405_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___boxed), 5, 0);
v___x_2406_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2407_ = lean_box(v_requireType_2396_);
v___x_2408_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitRightBracket_parenthesizer___boxed), 5, 0);
v___x_2410_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2410_, 0, v___x_2408_);
lean_closure_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2411_, 0, v___x_2406_);
lean_closure_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2412_, 0, v___x_2405_);
lean_closure_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2413_, 0, v___x_2412_);
v___x_2414_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2414_, 0, v___x_2402_);
lean_closure_set(v___x_2414_, 1, v___x_2404_);
lean_closure_set(v___x_2414_, 2, v___x_2413_);
v___x_2415_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2403_, v___x_2414_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed(lean_object* v_requireType_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
uint8_t v_requireType_boxed_2422_; lean_object* v_res_2423_; 
v_requireType_boxed_2422_ = lean_unbox(v_requireType_2416_);
v_res_2423_ = l_Lean_Parser_Term_strictImplicitBinder_parenthesizer(v_requireType_boxed_2422_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer(uint8_t v_requireType_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2437_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder___closed__1));
v___x_2438_ = ((lean_object*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___closed__0));
v___x_2439_ = lean_unsigned_to_nat(1024u);
v___x_2440_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket_parenthesizer___closed__0));
v___x_2441_ = lean_obj_once(&l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_explicitBinder_parenthesizer___closed__2);
v___x_2442_ = lean_box(v_requireType_2431_);
v___x_2443_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderType_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2443_, 0, v___x_2442_);
v___x_2444_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2444_, 0, v___x_2441_);
lean_closure_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2445_, 0, v___x_2444_);
v___x_2446_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer___closed__6));
v___x_2447_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2447_, 0, v___x_2445_);
lean_closure_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2448_, 0, v___x_2440_);
lean_closure_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2449_, 0, v___x_2448_);
v___x_2450_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2450_, 0, v___x_2437_);
lean_closure_set(v___x_2450_, 1, v___x_2439_);
lean_closure_set(v___x_2450_, 2, v___x_2449_);
v___x_2451_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2438_, v___x_2450_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed(lean_object* v_requireType_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
uint8_t v_requireType_boxed_2458_; lean_object* v_res_2459_; 
v_requireType_boxed_2458_ = lean_unbox(v_requireType_2452_);
v_res_2459_ = l_Lean_Parser_Term_implicitBinder_parenthesizer(v_requireType_boxed_2458_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer(lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___f_2468_; lean_object* v___x_2469_; 
v___f_2468_ = ((lean_object*)(l_Lean_Parser_Term_optIdent_parenthesizer___closed__0));
v___x_2469_ = l_Lean_Parser_optional_parenthesizer(v___f_2468_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optIdent_parenthesizer___boxed(lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Parser_Term_optIdent_parenthesizer(v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
return v_res_2475_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = ((lean_object*)(l_Lean_Parser_Term_binderType_parenthesizer___closed__1));
v___x_2486_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_parenthesizer___boxed), 5, 0);
v___x_2487_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2487_, 0, v___x_2486_);
lean_closure_set(v___x_2487_, 1, v___x_2485_);
return v___x_2487_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__2);
v___x_2489_ = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2489_, 0, v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__4));
v___x_2493_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__3, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__3);
v___x_2494_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2494_, 0, v___x_2493_);
lean_closure_set(v___x_2494_, 1, v___x_2492_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__5, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__5_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__5);
v___x_2496_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__1));
v___x_2497_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2497_, 0, v___x_2496_);
lean_closure_set(v___x_2497_, 1, v___x_2495_);
return v___x_2497_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__6, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__6_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__6);
v___x_2499_ = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2500_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__7, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__7);
v___x_2501_ = lean_unsigned_to_nat(1024u);
v___x_2502_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2503_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2503_, 0, v___x_2502_);
lean_closure_set(v___x_2503_, 1, v___x_2501_);
lean_closure_set(v___x_2503_, 2, v___x_2500_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer(lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = ((lean_object*)(l_Lean_Parser_Term_instBinder_parenthesizer___closed__0));
v___x_2510_ = lean_obj_once(&l_Lean_Parser_Term_instBinder_parenthesizer___closed__8, &l_Lean_Parser_Term_instBinder_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_instBinder_parenthesizer___closed__8);
v___x_2511_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2509_, v___x_2510_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_instBinder_parenthesizer___boxed(lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Parser_Term_instBinder_parenthesizer(v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37(){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2525_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2526_ = ((lean_object*)(l_Lean_Parser_Term_instBinder___closed__1));
v___x_2527_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___closed__0));
v___x_2528_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2529_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2525_, v___x_2526_, v___x_2527_, v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37___boxed(lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer(uint8_t v_requireType_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2544_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_parenthesizer___closed__0));
v___x_2545_ = lean_box(v_requireType_2538_);
v___x_2546_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_explicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2546_, 0, v___x_2545_);
v___x_2547_ = lean_box(v_requireType_2538_);
v___x_2548_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_strictImplicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2548_, 0, v___x_2547_);
v___x_2549_ = lean_box(v_requireType_2538_);
v___x_2550_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_implicitBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2550_, 0, v___x_2549_);
v___x_2551_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_instBinder_parenthesizer___boxed), 5, 0);
v___x_2552_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2552_, 0, v___x_2550_);
lean_closure_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2553_, 0, v___x_2548_);
lean_closure_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2554_, 0, v___x_2546_);
lean_closure_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2544_, v___x_2554_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object* v_requireType_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
uint8_t v_requireType_boxed_2562_; lean_object* v_res_2563_; 
v_requireType_boxed_2562_ = lean_unbox(v_requireType_2556_);
v_res_2563_ = l_Lean_Parser_Term_bracketedBinder_parenthesizer(v_requireType_boxed_2562_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2563_;
}
}
static lean_object* _init_l_Lean_Parser_Term_bracketedBinder___closed__0(void){
_start:
{
uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2564_ = 1;
v___x_2565_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2566_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__0));
v___x_2567_ = l_Lean_Parser_mkAntiquot(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2564_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t v_requireType_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2569_ = lean_obj_once(&l_Lean_Parser_Term_bracketedBinder___closed__0, &l_Lean_Parser_Term_bracketedBinder___closed__0_once, _init_l_Lean_Parser_Term_bracketedBinder___closed__0);
v___x_2570_ = l_Lean_Parser_Term_explicitBinder(v_requireType_2568_);
v___x_2571_ = l_Lean_Parser_Term_strictImplicitBinder(v_requireType_2568_);
v___x_2572_ = l_Lean_Parser_Term_implicitBinder(v_requireType_2568_);
v___x_2573_ = l_Lean_Parser_Term_instBinder;
v___x_2574_ = l_Lean_Parser_orelse(v___x_2572_, v___x_2573_);
v___x_2575_ = l_Lean_Parser_orelse(v___x_2571_, v___x_2574_);
v___x_2576_ = l_Lean_Parser_orelse(v___x_2570_, v___x_2575_);
v___x_2577_ = l_Lean_Parser_withAntiquot(v___x_2569_, v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___boxed(lean_object* v_requireType_2578_){
_start:
{
uint8_t v_requireType_boxed_2579_; lean_object* v_res_2580_; 
v_requireType_boxed_2579_ = lean_unbox(v_requireType_2578_);
v_res_2580_ = l_Lean_Parser_Term_bracketedBinder(v_requireType_boxed_2579_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1(){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder_formatter___closed__1));
v___x_2584_ = ((lean_object*)(l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___closed__0));
v___x_2585_ = l_Lean_addBuiltinDocString(v___x_2583_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1___boxed(lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter(lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__2));
v___x_2611_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__3));
v___x_2612_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2610_, v___x_2611_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_formatter___boxed(lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Parser_Term_typeSpec_formatter(v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3(){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2626_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2627_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2628_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___closed__0));
v___x_2629_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2630_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2626_, v___x_2627_, v___x_2628_, v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3___boxed(lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer(lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__0));
v___x_2650_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_parenthesizer___closed__1));
v___x_2651_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2649_, v___x_2650_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec_parenthesizer___boxed(lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Parser_Term_typeSpec_parenthesizer(v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7(){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2665_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2666_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2667_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___closed__0));
v___x_2668_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2669_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2665_, v___x_2666_, v___x_2667_, v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7___boxed(lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
return v_res_2671_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__0(void){
_start:
{
uint8_t v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2672_ = 0;
v___x_2673_ = 1;
v___x_2674_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2675_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__0));
v___x_2676_ = l_Lean_Parser_mkAntiquot(v___x_2675_, v___x_2674_, v___x_2673_, v___x_2672_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__1(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2677_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__2, &l_Lean_Parser_Term_binderType___closed__2_once, _init_l_Lean_Parser_Term_binderType___closed__2);
v___x_2678_ = lean_unsigned_to_nat(1024u);
v___x_2679_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2680_ = l_Lean_Parser_leadingNode(v___x_2679_, v___x_2678_, v___x_2677_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__2(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__1, &l_Lean_Parser_Term_typeSpec___closed__1_once, _init_l_Lean_Parser_Term_typeSpec___closed__1);
v___x_2682_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__0, &l_Lean_Parser_Term_typeSpec___closed__0_once, _init_l_Lean_Parser_Term_typeSpec___closed__0);
v___x_2683_ = l_Lean_Parser_withAntiquot(v___x_2682_, v___x_2681_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec___closed__3(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__2, &l_Lean_Parser_Term_typeSpec___closed__2_once, _init_l_Lean_Parser_Term_typeSpec___closed__2);
v___x_2685_ = ((lean_object*)(l_Lean_Parser_Term_typeSpec_formatter___closed__1));
v___x_2686_ = l_Lean_Parser_withCache(v___x_2685_, v___x_2684_);
return v___x_2686_;
}
}
static lean_object* _init_l_Lean_Parser_Term_typeSpec(void){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_obj_once(&l_Lean_Parser_Term_typeSpec___closed__3, &l_Lean_Parser_Term_typeSpec___closed__3_once, _init_l_Lean_Parser_Term_typeSpec___closed__3);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter(lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_2694_ = l_Lean_Parser_optional_formatter(v___x_2693_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_formatter___boxed(lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_Parser_Term_optType_formatter(v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer(lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___x_2707_ = l_Lean_Parser_optional_parenthesizer(v___x_2706_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optType_parenthesizer___boxed(lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Parser_Term_optType_parenthesizer(v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
return v_res_2713_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType___closed__0(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = l_Lean_Parser_Term_typeSpec;
v___x_2715_ = l_Lean_Parser_optional(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optType(void){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_obj_once(&l_Lean_Parser_Term_optType___closed__0, &l_Lean_Parser_Term_optType___closed__0_once, _init_l_Lean_Parser_Term_optType___closed__0);
return v___x_2716_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = lean_unsigned_to_nat(2382944618u);
v___x_2748_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__10_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2749_ = l_Lean_Name_num___override(v___x_2748_, v___x_2747_);
return v___x_2749_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2751_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__11_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2752_ = l_Lean_Name_str___override(v___x_2751_, v___x_2750_);
return v___x_2752_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Term_Basic_1563126128____hygCtx___hyg_2_));
v___x_2754_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__12_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2755_ = l_Lean_Name_str___override(v___x_2754_, v___x_2753_);
return v___x_2755_;
}
}
static lean_object* _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_unsigned_to_nat(2u);
v___x_2757_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__13_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2758_ = l_Lean_Name_num___override(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__1_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2761_ = ((lean_object*)(l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__3_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_));
v___x_2762_ = 0;
v___x_2763_ = lean_obj_once(&l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_, &l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn___closed__14_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_);
v___x_2764_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_2760_, v___x_2761_, v___x_2762_, v___x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2____boxed(lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser(lean_object* v_rbp_2769_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_2771_ = l_Lean_Parser_categoryParser(v___x_2770_, v_rbp_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter(lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__2));
v___x_2800_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__6));
v___x_2801_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2799_, v___x_2800_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_formatter___boxed(lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Parser_Term_optEllipsis_formatter(v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3(){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2815_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2816_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2817_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___closed__0));
v___x_2818_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_formatter___boxed), 5, 0);
v___x_2819_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2815_, v___x_2816_, v___x_2817_, v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3___boxed(lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer(lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__0));
v___x_2843_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___closed__3));
v___x_2844_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2842_, v___x_2843_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed(lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Parser_Term_optEllipsis_parenthesizer(v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7(){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2858_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2859_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2860_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___closed__0));
v___x_2861_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optEllipsis_parenthesizer___boxed), 5, 0);
v___x_2862_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2858_, v___x_2859_, v___x_2860_, v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7___boxed(lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
return v_res_2864_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__0(void){
_start:
{
uint8_t v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2865_ = 0;
v___x_2866_ = 1;
v___x_2867_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2868_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__0));
v___x_2869_ = l_Lean_Parser_mkAntiquot(v___x_2868_, v___x_2867_, v___x_2866_, v___x_2865_);
return v___x_2869_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__1(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__3));
v___x_2871_ = l_Lean_Parser_symbol(v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__2(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__1, &l_Lean_Parser_Term_optEllipsis___closed__1_once, _init_l_Lean_Parser_Term_optEllipsis___closed__1);
v___x_2873_ = l_Lean_Parser_optional(v___x_2872_);
return v___x_2873_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__3(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__2, &l_Lean_Parser_Term_optEllipsis___closed__2_once, _init_l_Lean_Parser_Term_optEllipsis___closed__2);
v___x_2875_ = lean_unsigned_to_nat(1024u);
v___x_2876_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2877_ = l_Lean_Parser_leadingNode(v___x_2876_, v___x_2875_, v___x_2874_);
return v___x_2877_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__4(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__3, &l_Lean_Parser_Term_optEllipsis___closed__3_once, _init_l_Lean_Parser_Term_optEllipsis___closed__3);
v___x_2879_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__0, &l_Lean_Parser_Term_optEllipsis___closed__0_once, _init_l_Lean_Parser_Term_optEllipsis___closed__0);
v___x_2880_ = l_Lean_Parser_withAntiquot(v___x_2879_, v___x_2878_);
return v___x_2880_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis___closed__5(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__4, &l_Lean_Parser_Term_optEllipsis___closed__4_once, _init_l_Lean_Parser_Term_optEllipsis___closed__4);
v___x_2882_ = ((lean_object*)(l_Lean_Parser_Term_optEllipsis_formatter___closed__1));
v___x_2883_ = l_Lean_Parser_withCache(v___x_2882_, v___x_2881_);
return v___x_2883_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optEllipsis(void){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_obj_once(&l_Lean_Parser_Term_optEllipsis___closed__5, &l_Lean_Parser_Term_optEllipsis___closed__5_once, _init_l_Lean_Parser_Term_optEllipsis___closed__5);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter(lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__2));
v___x_2916_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__6));
v___x_2917_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2915_, v___x_2916_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_formatter___boxed(lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Parser_Term_structInstArrayRef_formatter(v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3(){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2931_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2932_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_2933_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___closed__0));
v___x_2934_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_2935_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2931_, v___x_2932_, v___x_2933_, v___x_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3___boxed(lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer(lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__0));
v___x_2963_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___closed__4));
v___x_2964_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2962_, v___x_2963_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed(lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Parser_Term_structInstArrayRef_parenthesizer(v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7(){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2978_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2979_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_2980_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___closed__0));
v___x_2981_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_2982_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2978_, v___x_2979_, v___x_2980_, v___x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7___boxed(lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
return v_res_2984_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__0(void){
_start:
{
uint8_t v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2985_ = 0;
v___x_2986_ = 1;
v___x_2987_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_2988_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__0));
v___x_2989_ = l_Lean_Parser_mkAntiquot(v___x_2988_, v___x_2987_, v___x_2986_, v___x_2985_);
return v___x_2989_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__1(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_obj_once(&l_Lean_Parser_Term_binderType___closed__1, &l_Lean_Parser_Term_binderType___closed__1_once, _init_l_Lean_Parser_Term_binderType___closed__1);
v___x_2991_ = l_Lean_Parser_withoutPosition(v___x_2990_);
return v___x_2991_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__2(void){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__8, &l_Lean_Parser_Term_instBinder___closed__8_once, _init_l_Lean_Parser_Term_instBinder___closed__8);
v___x_2993_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__1, &l_Lean_Parser_Term_structInstArrayRef___closed__1_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__1);
v___x_2994_ = l_Lean_Parser_andthen(v___x_2993_, v___x_2992_);
return v___x_2994_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__3(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__2, &l_Lean_Parser_Term_structInstArrayRef___closed__2_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__2);
v___x_2996_ = lean_obj_once(&l_Lean_Parser_Term_instBinder___closed__4, &l_Lean_Parser_Term_instBinder___closed__4_once, _init_l_Lean_Parser_Term_instBinder___closed__4);
v___x_2997_ = l_Lean_Parser_andthen(v___x_2996_, v___x_2995_);
return v___x_2997_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__4(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2998_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__3, &l_Lean_Parser_Term_structInstArrayRef___closed__3_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__3);
v___x_2999_ = lean_unsigned_to_nat(1024u);
v___x_3000_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3001_ = l_Lean_Parser_leadingNode(v___x_3000_, v___x_2999_, v___x_2998_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__5(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__4, &l_Lean_Parser_Term_structInstArrayRef___closed__4_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__4);
v___x_3003_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__0, &l_Lean_Parser_Term_structInstArrayRef___closed__0_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__0);
v___x_3004_ = l_Lean_Parser_withAntiquot(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef___closed__6(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__5, &l_Lean_Parser_Term_structInstArrayRef___closed__5_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__5);
v___x_3006_ = ((lean_object*)(l_Lean_Parser_Term_structInstArrayRef_formatter___closed__1));
v___x_3007_ = l_Lean_Parser_withCache(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstArrayRef(void){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_obj_once(&l_Lean_Parser_Term_structInstArrayRef___closed__6, &l_Lean_Parser_Term_structInstArrayRef___closed__6_once, _init_l_Lean_Parser_Term_structInstArrayRef___closed__6);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3023_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3024_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3024_, 0, v___x_3023_);
lean_closure_set(v___x_3024_, 1, v___x_3022_);
return v___x_3024_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__3, &l_Lean_Parser_Term_structInstLVal_formatter___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__3);
v___x_3026_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3027_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3027_, 0, v___x_3026_);
lean_closure_set(v___x_3027_, 1, v___x_3025_);
return v___x_3027_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___boxed), 5, 0);
v___x_3032_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_formatter___closed__2));
v___x_3033_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3033_, 0, v___x_3032_);
lean_closure_set(v___x_3033_, 1, v___x_3031_);
return v___x_3033_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__7, &l_Lean_Parser_Term_structInstLVal_formatter___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__7);
v___x_3035_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__6));
v___x_3036_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3036_, 0, v___x_3035_);
lean_closure_set(v___x_3036_, 1, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__8, &l_Lean_Parser_Term_structInstLVal_formatter___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__8);
v___x_3038_ = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter___boxed), 6, 1);
lean_closure_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_formatter___boxed), 5, 0);
v___x_3040_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__9, &l_Lean_Parser_Term_structInstLVal_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__9);
v___x_3041_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3041_, 0, v___x_3040_);
lean_closure_set(v___x_3041_, 1, v___x_3039_);
return v___x_3041_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__10, &l_Lean_Parser_Term_structInstLVal_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__10);
v___x_3043_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__11, &l_Lean_Parser_Term_structInstLVal_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__11);
v___x_3045_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__4, &l_Lean_Parser_Term_structInstLVal_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__4);
v___x_3046_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3046_, 0, v___x_3045_);
lean_closure_set(v___x_3046_, 1, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__12, &l_Lean_Parser_Term_structInstLVal_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__12);
v___x_3048_ = lean_unsigned_to_nat(1024u);
v___x_3049_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3050_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3050_, 0, v___x_3049_);
lean_closure_set(v___x_3050_, 1, v___x_3048_);
lean_closure_set(v___x_3050_, 2, v___x_3047_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter(lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__2));
v___x_3057_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_formatter___closed__13, &l_Lean_Parser_Term_structInstLVal_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstLVal_formatter___closed__13);
v___x_3058_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3056_, v___x_3057_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_formatter___boxed(lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Parser_Term_structInstLVal_formatter(v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3(){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3072_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3073_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3074_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___closed__0));
v___x_3075_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3076_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3072_, v___x_3073_, v___x_3074_, v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3___boxed(lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_3080_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0___boxed(lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Parser_Term_structInstLVal_parenthesizer___lam__0(v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
return v_res_3090_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___f_3100_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__0));
v___x_3101_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3101_, 0, v___f_3100_);
lean_closure_set(v___x_3101_, 1, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__2);
v___x_3103_ = ((lean_object*)(l_Lean_Parser_Term_syntheticHole_parenthesizer___closed__2));
v___x_3104_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3104_, 0, v___x_3103_);
lean_closure_set(v___x_3104_, 1, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstArrayRef_parenthesizer___boxed), 5, 0);
v___x_3116_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__7));
v___x_3117_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3117_, 0, v___x_3116_);
lean_closure_set(v___x_3117_, 1, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__8);
v___x_3119_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3119_, 0, v___x_3118_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__9);
v___x_3121_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__3);
v___x_3122_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3122_, 0, v___x_3121_);
lean_closure_set(v___x_3122_, 1, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__10);
v___x_3124_ = lean_unsigned_to_nat(1024u);
v___x_3125_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3126_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3126_, 0, v___x_3125_);
lean_closure_set(v___x_3126_, 1, v___x_3124_);
lean_closure_set(v___x_3126_, 2, v___x_3123_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer(lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__1));
v___x_3133_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal_parenthesizer___closed__11);
v___x_3134_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3132_, v___x_3133_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed(lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Parser_Term_structInstLVal_parenthesizer(v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7(){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3148_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3149_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3150_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___closed__0));
v___x_3151_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3152_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3148_, v___x_3149_, v___x_3150_, v___x_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7___boxed(lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
return v_res_3154_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__0(void){
_start:
{
uint8_t v___x_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3155_ = 0;
v___x_3156_ = 1;
v___x_3157_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3158_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__0));
v___x_3159_ = l_Lean_Parser_mkAntiquot(v___x_3158_, v___x_3157_, v___x_3156_, v___x_3155_);
return v___x_3159_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__1(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3161_ = l_Lean_Parser_fieldIdx;
v___x_3162_ = l_Lean_Parser_orelse(v___x_3161_, v___x_3160_);
return v___x_3162_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__2(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__1, &l_Lean_Parser_Term_structInstLVal___closed__1_once, _init_l_Lean_Parser_Term_structInstLVal___closed__1);
v___x_3164_ = l_Lean_Parser_ident;
v___x_3165_ = l_Lean_Parser_orelse(v___x_3164_, v___x_3163_);
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__3(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__5));
v___x_3167_ = l_Lean_Parser_symbol(v___x_3166_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__4(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = l_Lean_Parser_fieldIdx;
v___x_3169_ = l_Lean_Parser_ident;
v___x_3170_ = l_Lean_Parser_orelse(v___x_3169_, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__5(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__4, &l_Lean_Parser_Term_structInstLVal___closed__4_once, _init_l_Lean_Parser_Term_structInstLVal___closed__4);
v___x_3172_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__3, &l_Lean_Parser_Term_structInstLVal___closed__3_once, _init_l_Lean_Parser_Term_structInstLVal___closed__3);
v___x_3173_ = l_Lean_Parser_andthen(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__6(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__5, &l_Lean_Parser_Term_structInstLVal___closed__5_once, _init_l_Lean_Parser_Term_structInstLVal___closed__5);
v___x_3175_ = ((lean_object*)(l_Lean_Parser_Term_strictImplicitLeftBracket___closed__2));
v___x_3176_ = l_Lean_Parser_node(v___x_3175_, v___x_3174_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__7(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = l_Lean_Parser_Term_structInstArrayRef;
v___x_3178_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__6, &l_Lean_Parser_Term_structInstLVal___closed__6_once, _init_l_Lean_Parser_Term_structInstLVal___closed__6);
v___x_3179_ = l_Lean_Parser_orelse(v___x_3178_, v___x_3177_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__8(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__7, &l_Lean_Parser_Term_structInstLVal___closed__7_once, _init_l_Lean_Parser_Term_structInstLVal___closed__7);
v___x_3181_ = l_Lean_Parser_many(v___x_3180_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__9(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__8, &l_Lean_Parser_Term_structInstLVal___closed__8_once, _init_l_Lean_Parser_Term_structInstLVal___closed__8);
v___x_3183_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__2, &l_Lean_Parser_Term_structInstLVal___closed__2_once, _init_l_Lean_Parser_Term_structInstLVal___closed__2);
v___x_3184_ = l_Lean_Parser_andthen(v___x_3183_, v___x_3182_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__10(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3185_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__9, &l_Lean_Parser_Term_structInstLVal___closed__9_once, _init_l_Lean_Parser_Term_structInstLVal___closed__9);
v___x_3186_ = lean_unsigned_to_nat(1024u);
v___x_3187_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3188_ = l_Lean_Parser_leadingNode(v___x_3187_, v___x_3186_, v___x_3185_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__11(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__10, &l_Lean_Parser_Term_structInstLVal___closed__10_once, _init_l_Lean_Parser_Term_structInstLVal___closed__10);
v___x_3190_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__0, &l_Lean_Parser_Term_structInstLVal___closed__0_once, _init_l_Lean_Parser_Term_structInstLVal___closed__0);
v___x_3191_ = l_Lean_Parser_withAntiquot(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal___closed__12(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__11, &l_Lean_Parser_Term_structInstLVal___closed__11_once, _init_l_Lean_Parser_Term_structInstLVal___closed__11);
v___x_3193_ = ((lean_object*)(l_Lean_Parser_Term_structInstLVal_formatter___closed__1));
v___x_3194_ = l_Lean_Parser_withCache(v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstLVal(void){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_obj_once(&l_Lean_Parser_Term_structInstLVal___closed__12, &l_Lean_Parser_Term_structInstLVal___closed__12_once, _init_l_Lean_Parser_Term_structInstLVal___closed__12);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__3));
v___x_3212_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter___boxed), 5, 0);
v___x_3213_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_3213_, 0, v___x_3212_);
lean_closure_set(v___x_3213_, 1, v___x_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter(lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__2));
v___x_3220_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4, &l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__4);
v___x_3221_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3219_, v___x_3220_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed(lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Parser_Term_structInstFieldBinder_formatter(v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
return v_res_3227_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__1));
v___x_3238_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer___boxed), 5, 0);
v___x_3239_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3239_, 0, v___x_3238_);
lean_closure_set(v___x_3239_, 1, v___x_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__0));
v___x_3246_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___closed__2);
v___x_3247_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_3245_, v___x_3246_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed(lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_Parser_Term_structInstFieldBinder_parenthesizer(v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
return v_res_3253_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0(void){
_start:
{
uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3254_ = 1;
v___x_3255_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__1));
v___x_3256_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___closed__0));
v___x_3257_ = l_Lean_Parser_mkAntiquot(v___x_3256_, v___x_3255_, v___x_3254_, v___x_3254_);
return v___x_3257_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1(void){
_start:
{
uint8_t v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = 0;
v___x_3259_ = l_Lean_Parser_Term_bracketedBinder(v___x_3258_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__1, &l_Lean_Parser_Term_structInstFieldBinder___closed__1_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__1);
v___x_3261_ = l_Lean_Parser_Term_binderIdent;
v___x_3262_ = l_Lean_Parser_orelse(v___x_3261_, v___x_3260_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__2, &l_Lean_Parser_Term_structInstFieldBinder___closed__2_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__2);
v___x_3264_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__0, &l_Lean_Parser_Term_structInstFieldBinder___closed__0_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__0);
v___x_3265_ = l_Lean_Parser_withAntiquot(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstFieldBinder(void){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_obj_once(&l_Lean_Parser_Term_structInstFieldBinder___closed__3, &l_Lean_Parser_Term_structInstFieldBinder___closed__3_once, _init_l_Lean_Parser_Term_structInstFieldBinder___closed__3);
return v___x_3266_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__0));
v___x_3270_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_formatter___boxed), 5, 0);
v___x_3271_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3271_, 0, v___x_3270_);
lean_closure_set(v___x_3271_, 1, v___x_3269_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__1);
v___x_3273_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter(lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2, &l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst_formatter___closed__2);
v___x_3280_ = l_Lean_Parser_optional_formatter(v___x_3279_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed(lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Parser_Term_optTypeForStructInst_formatter(v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
return v_res_3286_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___f_3291_; 
v___x_3289_ = ((lean_object*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__0));
v___x_3290_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_typeSpec_parenthesizer___boxed), 5, 0);
v___f_3291_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderTactic_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3291_, 0, v___x_3290_);
lean_closure_set(v___f_3291_, 1, v___x_3289_);
return v___f_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v___f_3297_; lean_object* v___x_3298_; 
v___f_3297_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1, &l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___closed__1);
v___x_3298_ = l_Lean_Parser_optional_parenthesizer(v___f_3297_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed(lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Parser_Term_optTypeForStructInst_parenthesizer(v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3304_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticSeqBracketed___closed__6));
v___x_3306_ = lean_obj_once(&l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7, &l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7_once, _init_l_Lean_Parser_Tactic_tacticSeqBracketed___closed__7);
v___x_3307_ = l_Lean_Parser_notFollowedBy(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__0, &l_Lean_Parser_Term_optTypeForStructInst___closed__0_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__0);
v___x_3309_ = l_Lean_Parser_Term_typeSpec;
v___x_3310_ = l_Lean_Parser_andthen(v___x_3309_, v___x_3308_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__1, &l_Lean_Parser_Term_optTypeForStructInst___closed__1_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__1);
v___x_3312_ = l_Lean_Parser_atomic(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__2, &l_Lean_Parser_Term_optTypeForStructInst___closed__2_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__2);
v___x_3314_ = l_Lean_Parser_optional(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_Parser_Term_optTypeForStructInst(void){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_obj_once(&l_Lean_Parser_Term_optTypeForStructInst___closed__3, &l_Lean_Parser_Term_optTypeForStructInst___closed__3_once, _init_l_Lean_Parser_Term_optTypeForStructInst___closed__3);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3322_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_3321_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg___boxed(lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter(lean_object* v_rbp_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter___redArg(v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_formatter___boxed(lean_object* v_rbp_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Parser_Term_structInstFieldDeclParser_formatter(v_rbp_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_rbp_3336_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0(lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3344_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__0___boxed(lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_Parser_Term_structInstField_formatter___lam__0(v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1(lean_object* v___x_3355_, lean_object* v___x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_3355_, v___x_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed(lean_object* v___x_3363_, lean_object* v___x_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Parser_Term_structInstField_formatter___lam__1(v___x_3363_, v___x_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
return v_res_3370_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__4(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; 
v___x_3385_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_formatter___boxed), 5, 0);
v___f_3386_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__0));
v___x_3387_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3387_, 0, v___f_3386_);
lean_closure_set(v___x_3387_, 1, v___x_3385_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__5(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__4, &l_Lean_Parser_Term_structInstField_formatter___closed__4_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__4);
v___x_3389_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
v___x_3390_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3390_, 0, v___x_3389_);
lean_closure_set(v___x_3390_, 1, v___x_3388_);
return v___x_3390_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__6(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__5, &l_Lean_Parser_Term_structInstField_formatter___closed__5_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__5);
v___x_3392_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__9(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__8));
v___x_3398_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_formatter___boxed), 5, 0);
v___x_3399_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3399_, 0, v___x_3398_);
lean_closure_set(v___x_3399_, 1, v___x_3397_);
return v___x_3399_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__10(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__9, &l_Lean_Parser_Term_structInstField_formatter___closed__9_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__9);
v___x_3401_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__6, &l_Lean_Parser_Term_structInstField_formatter___closed__6_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__6);
v___x_3402_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3402_, 0, v___x_3401_);
lean_closure_set(v___x_3402_, 1, v___x_3400_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__11(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__10, &l_Lean_Parser_Term_structInstField_formatter___closed__10_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__10);
v___x_3404_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__12(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__11, &l_Lean_Parser_Term_structInstField_formatter___closed__11_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__11);
v___x_3406_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_formatter___boxed), 5, 0);
v___x_3407_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_3407_, 0, v___x_3406_);
lean_closure_set(v___x_3407_, 1, v___x_3405_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__13(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3408_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__12, &l_Lean_Parser_Term_structInstField_formatter___closed__12_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__12);
v___x_3409_ = lean_unsigned_to_nat(1024u);
v___x_3410_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3411_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_3411_, 0, v___x_3410_);
lean_closure_set(v___x_3411_, 1, v___x_3409_);
lean_closure_set(v___x_3411_, 2, v___x_3408_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__14(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___f_3414_; 
v___x_3412_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__13, &l_Lean_Parser_Term_structInstField_formatter___closed__13_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__13);
v___x_3413_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__3));
v___f_3414_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___lam__1___boxed), 7, 2);
lean_closure_set(v___f_3414_, 0, v___x_3413_);
lean_closure_set(v___f_3414_, 1, v___x_3412_);
return v___f_3414_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_formatter___closed__15(void){
_start:
{
lean_object* v___f_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___f_3415_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__14, &l_Lean_Parser_Term_structInstField_formatter___closed__14_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__14);
v___x_3416_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3417_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_formatter___boxed), 7, 2);
lean_closure_set(v___x_3417_, 0, v___x_3416_);
lean_closure_set(v___x_3417_, 1, v___f_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter(lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_formatter___closed__15, &l_Lean_Parser_Term_structInstField_formatter___closed__15_once, _init_l_Lean_Parser_Term_structInstField_formatter___closed__15);
v___x_3424_ = l_Lean_Parser_ppGroup_formatter(v___x_3423_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Parser_Term_structInstField_formatter(v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec(v_a_3426_);
lean_dec_ref(v_a_3425_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5(){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3438_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3439_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3440_ = ((lean_object*)(l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___closed__0));
v___x_3441_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter___boxed), 5, 0);
v___x_3442_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3438_, v___x_3439_, v___x_3440_, v___x_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5___boxed(lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(lean_object* v_rbp_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3452_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_3451_, v_rbp_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer___boxed(lean_object* v_rbp_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Parser_Term_structInstFieldDeclParser_parenthesizer(v_rbp_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
return v_res_3459_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstFieldBinder_parenthesizer___boxed), 5, 0);
v___x_3469_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__1));
v___x_3470_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3470_, 0, v___x_3469_);
lean_closure_set(v___x_3470_, 1, v___x_3468_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__2, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__2_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__2);
v___x_3472_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
v___x_3473_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3473_, 0, v___x_3472_);
lean_closure_set(v___x_3473_, 1, v___x_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__3, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__3_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__3);
v___x_3475_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__6));
v___x_3481_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_optTypeForStructInst_parenthesizer___boxed), 5, 0);
v___x_3482_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3482_, 0, v___x_3481_);
lean_closure_set(v___x_3482_, 1, v___x_3480_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__7, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__7_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__7);
v___x_3484_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__4, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__4_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__4);
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3485_, 0, v___x_3484_);
lean_closure_set(v___x_3485_, 1, v___x_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__8, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__8_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__8);
v___x_3487_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__9, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__9_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__9);
v___x_3489_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstLVal_parenthesizer___boxed), 5, 0);
v___x_3490_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3490_, 0, v___x_3489_);
lean_closure_set(v___x_3490_, 1, v___x_3488_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3491_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__10, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__10_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__10);
v___x_3492_ = lean_unsigned_to_nat(1024u);
v___x_3493_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3494_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_3494_, 0, v___x_3493_);
lean_closure_set(v___x_3494_, 1, v___x_3492_);
lean_closure_set(v___x_3494_, 2, v___x_3491_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__11, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__11_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__11);
v___x_3496_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_parenthesizer___closed__0));
v___x_3497_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3497_, 0, v___x_3496_);
lean_closure_set(v___x_3497_, 1, v___x_3495_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__12, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__12_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__12);
v___x_3499_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3500_ = lean_alloc_closure((void*)(l_Lean_Parser_withCache_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_3500_, 0, v___x_3499_);
lean_closure_set(v___x_3500_, 1, v___x_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer(lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_obj_once(&l_Lean_Parser_Term_structInstField_parenthesizer___closed__13, &l_Lean_Parser_Term_structInstField_parenthesizer___closed__13_once, _init_l_Lean_Parser_Term_structInstField_parenthesizer___closed__13);
v___x_3507_ = l_Lean_Parser_ppGroup_parenthesizer(v___x_3506_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Parser_Term_structInstField_parenthesizer(v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11(){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3521_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_3522_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3523_ = ((lean_object*)(l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___closed__0));
v___x_3524_ = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_parenthesizer___boxed), 5, 0);
v___x_3525_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3521_, v___x_3522_, v___x_3523_, v___x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11___boxed(lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
return v_res_3527_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__0(void){
_start:
{
uint8_t v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3528_ = 0;
v___x_3529_ = 1;
v___x_3530_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3531_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__1));
v___x_3532_ = l_Lean_Parser_mkAntiquot(v___x_3531_, v___x_3530_, v___x_3529_, v___x_3528_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__2(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l_Lean_Parser_Term_structInstField___closed__1));
v___x_3535_ = l_Lean_Parser_checkColGt(v___x_3534_);
return v___x_3535_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__3(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = l_Lean_Parser_Term_structInstFieldBinder;
v___x_3537_ = l_Lean_Parser_skip;
v___x_3538_ = l_Lean_Parser_andthen(v___x_3537_, v___x_3536_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__4(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__3, &l_Lean_Parser_Term_structInstField___closed__3_once, _init_l_Lean_Parser_Term_structInstField___closed__3);
v___x_3540_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__2, &l_Lean_Parser_Term_structInstField___closed__2_once, _init_l_Lean_Parser_Term_structInstField___closed__2);
v___x_3541_ = l_Lean_Parser_andthen(v___x_3540_, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__5(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__4, &l_Lean_Parser_Term_structInstField___closed__4_once, _init_l_Lean_Parser_Term_structInstField___closed__4);
v___x_3543_ = l_Lean_Parser_many(v___x_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__6(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = lean_unsigned_to_nat(0u);
v___x_3545_ = ((lean_object*)(l_Lean_Parser_Term_structInstFieldDeclParser___closed__0));
v___x_3546_ = l_Lean_Parser_categoryParser(v___x_3545_, v___x_3544_);
return v___x_3546_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__7(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__6, &l_Lean_Parser_Term_structInstField___closed__6_once, _init_l_Lean_Parser_Term_structInstField___closed__6);
v___x_3548_ = l_Lean_Parser_Term_optTypeForStructInst;
v___x_3549_ = l_Lean_Parser_andthen(v___x_3548_, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__8(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__7, &l_Lean_Parser_Term_structInstField___closed__7_once, _init_l_Lean_Parser_Term_structInstField___closed__7);
v___x_3551_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__5, &l_Lean_Parser_Term_structInstField___closed__5_once, _init_l_Lean_Parser_Term_structInstField___closed__5);
v___x_3552_ = l_Lean_Parser_andthen(v___x_3551_, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__9(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__8, &l_Lean_Parser_Term_structInstField___closed__8_once, _init_l_Lean_Parser_Term_structInstField___closed__8);
v___x_3554_ = l_Lean_Parser_optional(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__10(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__9, &l_Lean_Parser_Term_structInstField___closed__9_once, _init_l_Lean_Parser_Term_structInstField___closed__9);
v___x_3556_ = l_Lean_Parser_Term_structInstLVal;
v___x_3557_ = l_Lean_Parser_andthen(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__11(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3558_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__10, &l_Lean_Parser_Term_structInstField___closed__10_once, _init_l_Lean_Parser_Term_structInstField___closed__10);
v___x_3559_ = lean_unsigned_to_nat(1024u);
v___x_3560_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3561_ = l_Lean_Parser_leadingNode(v___x_3560_, v___x_3559_, v___x_3558_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__12(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__11, &l_Lean_Parser_Term_structInstField___closed__11_once, _init_l_Lean_Parser_Term_structInstField___closed__11);
v___x_3563_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__0, &l_Lean_Parser_Term_structInstField___closed__0_once, _init_l_Lean_Parser_Term_structInstField___closed__0);
v___x_3564_ = l_Lean_Parser_withAntiquot(v___x_3563_, v___x_3562_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField___closed__13(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__12, &l_Lean_Parser_Term_structInstField___closed__12_once, _init_l_Lean_Parser_Term_structInstField___closed__12);
v___x_3566_ = ((lean_object*)(l_Lean_Parser_Term_structInstField_formatter___closed__2));
v___x_3567_ = l_Lean_Parser_withCache(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Parser_Term_structInstField(void){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_obj_once(&l_Lean_Parser_Term_structInstField___closed__13, &l_Lean_Parser_Term_structInstField___closed__13_once, _init_l_Lean_Parser_Term_structInstField___closed__13);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object* v_p_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3582_ = l_Lean_PrettyPrinter_Formatter_node_formatter(v___x_3581_, v_p_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_formatter___boxed(lean_object* v_p_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Parser_Term_structInstFields_formatter(v_p_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object* v_p_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3597_ = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(v___x_3596_, v_p_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer___boxed(lean_object* v_p_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v_p_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_structInstFields(lean_object* v_p_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = ((lean_object*)(l_Lean_Parser_Term_structInstFields_formatter___closed__1));
v___x_3607_ = l_Lean_Parser_node(v___x_3606_, v_p_3605_);
return v___x_3607_;
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
res = l_Lean_Parser_Tactic_sepByIndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepByIndentSemicolon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_sepBy1IndentSemicolon___regBuiltin_Lean_Parser_Tactic_sepBy1IndentSemicolon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Term_Basic_1911936479____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticSeq1Indented = _init_l_Lean_Parser_Tactic_tacticSeq1Indented();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeq1Indented);
l_Lean_Parser_Tactic_tacticSeqBracketed = _init_l_Lean_Parser_Tactic_tacticSeqBracketed();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeqBracketed);
res = l_Lean_Parser_Tactic_tacticSeqBracketed___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_formatter__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_formatter__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq1Indented_parenthesizer__23();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_parenthesizer__27();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticSeq = _init_l_Lean_Parser_Tactic_tacticSeq();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeq);
res = l_Lean_Parser_Tactic_tacticSeq___regBuiltin_Lean_Parser_Tactic_tacticSeq_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_tacticSeqIndentGt = _init_l_Lean_Parser_Tactic_tacticSeqIndentGt();
lean_mark_persistent(l_Lean_Parser_Tactic_tacticSeqIndentGt);
res = l_Lean_Parser_Tactic_tacticSeqIndentGt___regBuiltin_Lean_Parser_Tactic_tacticSeqIndentGt_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Tactic_seq1___regBuiltin_Lean_Parser_Tactic_seq1_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_seq1 = _init_l_Lean_Parser_Tactic_seq1();
lean_mark_persistent(l_Lean_Parser_Tactic_seq1);
l_Lean_Parser_Term_hole = _init_l_Lean_Parser_Term_hole();
lean_mark_persistent(l_Lean_Parser_Term_hole);
res = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_hole___regBuiltin_Lean_Parser_Term_hole_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_syntheticHole = _init_l_Lean_Parser_Term_syntheticHole();
lean_mark_persistent(l_Lean_Parser_Term_syntheticHole);
res = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_syntheticHole___regBuiltin_Lean_Parser_Term_syntheticHole_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_omission = _init_l_Lean_Parser_Term_omission();
lean_mark_persistent(l_Lean_Parser_Term_omission);
res = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_omission___regBuiltin_Lean_Parser_Term_omission_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_binderIdent = _init_l_Lean_Parser_Term_binderIdent();
lean_mark_persistent(l_Lean_Parser_Term_binderIdent);
res = l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_binderTactic___regBuiltin_Lean_Parser_Term_binderTactic_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_binderTactic = _init_l_Lean_Parser_Term_binderTactic();
lean_mark_persistent(l_Lean_Parser_Term_binderTactic);
l_Lean_Parser_Term_binderDefault = _init_l_Lean_Parser_Term_binderDefault();
lean_mark_persistent(l_Lean_Parser_Term_binderDefault);
res = l_Lean_Parser_Term_explicitBinder___regBuiltin_Lean_Parser_Term_explicitBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_implicitBinder___regBuiltin_Lean_Parser_Term_implicitBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_strictImplicitLeftBracket = _init_l_Lean_Parser_Term_strictImplicitLeftBracket();
lean_mark_persistent(l_Lean_Parser_Term_strictImplicitLeftBracket);
l_Lean_Parser_Term_strictImplicitRightBracket = _init_l_Lean_Parser_Term_strictImplicitRightBracket();
lean_mark_persistent(l_Lean_Parser_Term_strictImplicitRightBracket);
res = l_Lean_Parser_Term_strictImplicitBinder___regBuiltin_Lean_Parser_Term_strictImplicitBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_optIdent = _init_l_Lean_Parser_Term_optIdent();
lean_mark_persistent(l_Lean_Parser_Term_optIdent);
l_Lean_Parser_Term_instBinder = _init_l_Lean_Parser_Term_instBinder();
lean_mark_persistent(l_Lean_Parser_Term_instBinder);
res = l_Lean_Parser_Term_instBinder___regBuiltin_Lean_Parser_Term_instBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_binderDefault_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_formatter__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_instBinder_parenthesizer__37();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_bracketedBinder___regBuiltin_Lean_Parser_Term_bracketedBinder_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_typeSpec___regBuiltin_Lean_Parser_Term_typeSpec_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_typeSpec = _init_l_Lean_Parser_Term_typeSpec();
lean_mark_persistent(l_Lean_Parser_Term_typeSpec);
l_Lean_Parser_Term_optType = _init_l_Lean_Parser_Term_optType();
lean_mark_persistent(l_Lean_Parser_Term_optType);
res = l___private_Lean_Parser_Term_Basic_0__Lean_Parser_Term_initFn_00___x40_Lean_Parser_Term_Basic_2382944618____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_optEllipsis___regBuiltin_Lean_Parser_Term_optEllipsis_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_optEllipsis = _init_l_Lean_Parser_Term_optEllipsis();
lean_mark_persistent(l_Lean_Parser_Term_optEllipsis);
res = l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_structInstArrayRef___regBuiltin_Lean_Parser_Term_structInstArrayRef_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_structInstArrayRef = _init_l_Lean_Parser_Term_structInstArrayRef();
lean_mark_persistent(l_Lean_Parser_Term_structInstArrayRef);
res = l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_formatter__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_structInstLVal___regBuiltin_Lean_Parser_Term_structInstLVal_parenthesizer__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Term_structInstLVal = _init_l_Lean_Parser_Term_structInstLVal();
lean_mark_persistent(l_Lean_Parser_Term_structInstLVal);
l_Lean_Parser_Term_structInstFieldBinder = _init_l_Lean_Parser_Term_structInstFieldBinder();
lean_mark_persistent(l_Lean_Parser_Term_structInstFieldBinder);
l_Lean_Parser_Term_optTypeForStructInst = _init_l_Lean_Parser_Term_optTypeForStructInst();
lean_mark_persistent(l_Lean_Parser_Term_optTypeForStructInst);
res = l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_formatter__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_Term_structInstField___regBuiltin_Lean_Parser_Term_structInstField_parenthesizer__11();
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
