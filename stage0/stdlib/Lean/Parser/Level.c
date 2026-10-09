// Lean compiler output
// Module: Lean.Parser.Level
// Imports: public import Lean.Parser.Extra
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
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_checkPrec(lean_object*);
lean_object* l_Lean_Parser_withoutPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "builtin_level_parser"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 234, 74, 98, 36, 143, 62, 135)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Category"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "level"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 194, 17, 31, 235, 221, 150, 77)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Level"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 141, 193, 245, 4, 108, 38, 201)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(101, 129, 115, 224, 25, 210, 10, 108)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 198, 243, 212, 167, 39, 82, 207)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 33, 1, 183, 106, 197, 214, 26)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 239, 151, 247, 236, 7, 237, 74)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 197, 214, 163, 241, 170, 166, 6)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 229, 174, 131, 68, 211, 141, 209)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 193, 198, 87, 122, 30, 172, 217)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 18, 31, 29, 40, 61, 243, 42)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l_Lean_Parser_levelParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(248, 87, 114, 95, 43, 103, 70, 253)}};
static const lean_object* l_Lean_Parser_levelParser___closed__0 = (const lean_object*)&l_Lean_Parser_levelParser___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser(lean_object*);
static const lean_string_object l_Lean_Parser_Level_paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Level_paren___closed__0 = (const lean_object*)&l_Lean_Parser_Level_paren___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Level_paren___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Level_paren___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Level_paren___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Parser_Level_paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_object* l_Lean_Parser_Level_paren___closed__1 = (const lean_object*)&l_Lean_Parser_Level_paren___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__2;
static const lean_string_object l_Lean_Parser_Level_paren___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Level_paren___closed__3 = (const lean_object*)&l_Lean_Parser_Level_paren___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__5;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__6;
static const lean_string_object l_Lean_Parser_Level_paren___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Level_paren___closed__7 = (const lean_object*)&l_Lean_Parser_Level_paren___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__8;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__9;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__10;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__11;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__12;
static lean_once_cell_t l_Lean_Parser_Level_paren___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_paren___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__0_value),((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__3_value)} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_levelParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__7_value)} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__3_value),((lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Level_paren_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Level_paren_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Level_paren_formatter___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 205, 143, 182, 150, 105, 121, 3)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__0_value),((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__3_value)} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_levelParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withoutPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__7_value)} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__3_value),((lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Level_paren_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Level_paren___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Level_paren_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Level_paren_parenthesizer___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 227, 175, 112, 158, 37, 38, 221)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Level_max___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l_Lean_Parser_Level_max___closed__0 = (const lean_object*)&l_Lean_Parser_Level_max___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Level_max___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Level_max___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Level_max___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Parser_Level_max___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_object* l_Lean_Parser_Level_max___closed__1 = (const lean_object*)&l_Lean_Parser_Level_max___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__2;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__3;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__5;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__6;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__7;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__8;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__9;
static lean_once_cell_t l_Lean_Parser_Level_max___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Level_max_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Level_max_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Level_max_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_max_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_max_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),((lean_object*)&l_Lean_Parser_Level_max___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_max_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Level_max_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Level_max_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_max_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Level_max_formatter___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Level_max_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Level_max_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_max_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Level_max_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Level_max_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_formatter___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 225, 183, 44, 175, 196, 165, 133)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_max_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),((lean_object*)&l_Lean_Parser_Level_max___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Level_max_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_max_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Level_max_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Level_max_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppSpace_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Level_max_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Level_max_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Level_max_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_max_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Level_max_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Parser_Level_max_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_max_parenthesizer___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_max___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 115, 250, 67, 104, 241, 13, 135)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Level_imax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l_Lean_Parser_Level_imax___closed__0 = (const lean_object*)&l_Lean_Parser_Level_imax___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Level_imax___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Level_imax___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Level_imax___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Parser_Level_imax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_object* l_Lean_Parser_Level_imax___closed__1 = (const lean_object*)&l_Lean_Parser_Level_imax___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Level_imax___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax___closed__2;
static lean_once_cell_t l_Lean_Parser_Level_imax___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax___closed__3;
static lean_once_cell_t l_Lean_Parser_Level_imax___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_imax___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax___closed__5;
static lean_once_cell_t l_Lean_Parser_Level_imax___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax___closed__6;
static lean_once_cell_t l_Lean_Parser_Level_imax___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_imax_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),((lean_object*)&l_Lean_Parser_Level_imax___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_imax_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_imax_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_imax_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_imax_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Level_imax_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Level_imax_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Level_imax_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 26, 255, 193, 194, 235, 233, 232)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_imax_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),((lean_object*)&l_Lean_Parser_Level_imax___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_imax_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Level_imax_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_imax_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_imax_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Level_imax_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Level_imax_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Level_imax_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_imax_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_imax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 81, 250, 139, 137, 13, 195, 65)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Level_hole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Parser_Level_hole___closed__0 = (const lean_object*)&l_Lean_Parser_Level_hole___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Level_hole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Level_hole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Level_hole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Parser_Level_hole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 86, 172, 30, 114, 81, 66, 18)}};
static const lean_object* l_Lean_Parser_Level_hole___closed__1 = (const lean_object*)&l_Lean_Parser_Level_hole___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Level_hole___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_hole___closed__2;
static const lean_string_object l_Lean_Parser_Level_hole___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_Level_hole___closed__3 = (const lean_object*)&l_Lean_Parser_Level_hole___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Level_hole___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_hole___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_hole___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_hole___closed__5;
static lean_once_cell_t l_Lean_Parser_Level_hole___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_hole___closed__6;
static lean_once_cell_t l_Lean_Parser_Level_hole___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_hole___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_hole_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__0_value),((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_hole_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_hole_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_hole_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Level_hole_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Level_hole_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Level_hole_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Level_hole_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Level_hole_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Level_hole_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 86, 172, 30, 114, 81, 66, 18)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 121, 29, 92, 225, 27, 180, 225)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_hole_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__0_value),((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Level_hole_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Level_hole_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_hole_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__3_value)} };
static const lean_object* l_Lean_Parser_Level_hole_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Level_hole_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Level_hole_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Level_hole___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Level_hole_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Level_hole_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Level_hole_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_hole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 86, 172, 30, 114, 81, 66, 18)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 66, 56, 8, 167, 106, 211, 138)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Level_num___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_num___closed__0;
static lean_once_cell_t l_Lean_Parser_Level_num___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_num___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 144, 149, 43, 79, 38, 134, 232)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1_value),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_num_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Level_num_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_num_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Level_num_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_num_parenthesizer___closed__0;
static const lean_closure_object l_Lean_Parser_Level_num_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Level_num_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Level_num_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Level_ident___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_ident___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident;
static const lean_string_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 196, 73, 63, 184, 149, 21, 131)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_ident_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Level_ident_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_ident_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Level_ident_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Level_ident_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Level_ident_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Level_addLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addLit"};
static const lean_object* l_Lean_Parser_Level_addLit___closed__0 = (const lean_object*)&l_Lean_Parser_Level_addLit___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Level_addLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Level_addLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Level_addLit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Parser_Level_addLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Level_addLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 243, 225, 2, 30, 243, 80, 174)}};
static const lean_object* l_Lean_Parser_Level_addLit___closed__1 = (const lean_object*)&l_Lean_Parser_Level_addLit___closed__1_value;
static const lean_string_object l_Lean_Parser_Level_addLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l_Lean_Parser_Level_addLit___closed__2 = (const lean_object*)&l_Lean_Parser_Level_addLit___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Level_addLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_addLit___closed__3;
static lean_once_cell_t l_Lean_Parser_Level_addLit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_addLit___closed__4;
static lean_once_cell_t l_Lean_Parser_Level_addLit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Level_addLit___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0_value),((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_addLit_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit___closed__2_value)} };
static const lean_object* l_Lean_Parser_Level_addLit_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Level_addLit_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_addLit_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Level_num_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Level_addLit_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Level_addLit_formatter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_addLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 243, 225, 2, 30, 243, 80, 174)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 138, 111, 75, 72, 230, 73, 52)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Level_addLit_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit___closed__2_value)} };
static const lean_object* l_Lean_Parser_Level_addLit_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Level_addLit_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Level_addLit_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Level_addLit_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Parser_Level_num_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Level_addLit_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Level_addLit_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Level_addLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 243, 225, 2, 30, 243, 80, 174)}};
static const lean_ctor_object l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 158, 100, 239, 198, 8, 217, 250)}};
static const lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___boxed(lean_object*);
static lean_object* _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_unsigned_to_nat(2271617841u);
v___x_54_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_));
v___x_55_ = l_Lean_Name_num___override(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_));
v___x_58_ = lean_obj_once(&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_, &l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
v___x_59_ = l_Lean_Name_str___override(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_));
v___x_62_ = lean_obj_once(&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_, &l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
v___x_63_ = l_Lean_Name_str___override(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_unsigned_to_nat(2u);
v___x_65_ = lean_obj_once(&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_, &l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
v___x_66_ = l_Lean_Name_num___override(v___x_65_, v___x_64_);
return v___x_66_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_));
v___x_69_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_));
v___x_70_ = 0;
v___x_71_ = lean_obj_once(&l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_, &l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
v___x_72_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_68_, v___x_69_, v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_73_;
v_res_73_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser(lean_object* v_rbp_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_80_ = l_Lean_Parser_categoryParser(v___x_79_, v_rbp_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__2(void){
_start:
{
uint8_t v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = 0;
v___x_88_ = 1;
v___x_89_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_90_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__0));
v___x_91_ = l_Lean_Parser_mkAntiquot(v___x_90_, v___x_89_, v___x_88_, v___x_87_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__4(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__3));
v___x_94_ = l_Lean_Parser_symbol(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__5(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_97_ = l_Lean_Parser_categoryParser(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__6(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__5, &l_Lean_Parser_Level_paren___closed__5_once, _init_l_Lean_Parser_Level_paren___closed__5);
v___x_99_ = l_Lean_Parser_withoutPosition(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__8(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__7));
v___x_102_ = l_Lean_Parser_symbol(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__9(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__8, &l_Lean_Parser_Level_paren___closed__8_once, _init_l_Lean_Parser_Level_paren___closed__8);
v___x_104_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__6, &l_Lean_Parser_Level_paren___closed__6_once, _init_l_Lean_Parser_Level_paren___closed__6);
v___x_105_ = l_Lean_Parser_andthen(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__10(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__9, &l_Lean_Parser_Level_paren___closed__9_once, _init_l_Lean_Parser_Level_paren___closed__9);
v___x_107_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__4, &l_Lean_Parser_Level_paren___closed__4_once, _init_l_Lean_Parser_Level_paren___closed__4);
v___x_108_ = l_Lean_Parser_andthen(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__11(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__10, &l_Lean_Parser_Level_paren___closed__10_once, _init_l_Lean_Parser_Level_paren___closed__10);
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_112_ = l_Lean_Parser_leadingNode(v___x_111_, v___x_110_, v___x_109_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__12(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__11, &l_Lean_Parser_Level_paren___closed__11_once, _init_l_Lean_Parser_Level_paren___closed__11);
v___x_114_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__2, &l_Lean_Parser_Level_paren___closed__2_once, _init_l_Lean_Parser_Level_paren___closed__2);
v___x_115_ = l_Lean_Parser_withAntiquot(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__13(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__12, &l_Lean_Parser_Level_paren___closed__12_once, _init_l_Lean_Parser_Level_paren___closed__12);
v___x_117_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_118_ = l_Lean_Parser_withCache(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__13, &l_Lean_Parser_Level_paren___closed__13_once, _init_l_Lean_Parser_Level_paren___closed__13);
return v___x_119_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1(){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_122_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_123_ = l_Lean_Parser_Level_paren;
v___x_124_ = lean_unsigned_to_nat(1000u);
v___x_125_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_121_, v___x_122_, v___x_123_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_126_;
v_res_126_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1___boxed(lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
return v_res_128_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3(){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_156_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6));
v___x_157_ = l_Lean_addBuiltinDeclarationRanges(v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_158_;
v_res_158_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___boxed(lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
return v_res_160_;
}
}
lean_object* l_Lean_Parser_levelParser_formatter___redArg(lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_167_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_166_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Lean_Parser_levelParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_161_ = stack[0].m_obj;
lean_object* v_a_162_ = stack[1].m_obj;
lean_object* v_a_163_ = stack[2].m_obj;
lean_object* v_a_164_ = stack[3].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Parser_levelParser_formatter___redArg(v_a_161_, v_a_162_, v_a_163_, v_a_164_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___redArg___boxed(lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Parser_levelParser_formatter___redArg(v_a_169_, v_a_170_, v_a_171_, v_a_172_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_174_;
}
}
lean_object* l_Lean_Parser_levelParser_formatter(lean_object* v_rbp_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Parser_levelParser_formatter___redArg(v_a_176_, v_a_177_, v_a_178_, v_a_179_);
return v___x_181_;
}
}
LEAN_EXPORT void l_Lean_Parser_levelParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_175_ = stack[0].m_obj;
lean_object* v_a_176_ = stack[1].m_obj;
lean_object* v_a_177_ = stack[2].m_obj;
lean_object* v_a_178_ = stack[3].m_obj;
lean_object* v_a_179_ = stack[4].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_Lean_Parser_levelParser_formatter(v_rbp_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___boxed(lean_object* v_rbp_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Parser_levelParser_formatter(v_rbp_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_rbp_183_);
return v_res_189_;
}
}
lean_object* l_Lean_Parser_Level_paren_formatter(lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((lean_object*)(l_Lean_Parser_Level_paren_formatter___closed__0));
v___x_221_ = ((lean_object*)(l_Lean_Parser_Level_paren_formatter___closed__7));
v___x_222_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_220_, v___x_221_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
return v___x_222_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_paren_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_215_ = stack[0].m_obj;
lean_object* v_a_216_ = stack[1].m_obj;
lean_object* v_a_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_Lean_Parser_Level_paren_formatter(v_a_215_, v_a_216_, v_a_217_, v_a_218_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_formatter___boxed(lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Parser_Level_paren_formatter(v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_229_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9(){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_239_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_240_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1));
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_paren_formatter___boxed), 5, 0);
v___x_242_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_238_, v___x_239_, v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_243_;
v_res_243_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
return v_res_245_;
}
}
lean_object* l_Lean_Parser_levelParser_parenthesizer(lean_object* v_rbp_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_253_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_252_, v_rbp_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Lean_Parser_levelParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_246_ = stack[0].m_obj;
lean_object* v_a_247_ = stack[1].m_obj;
lean_object* v_a_248_ = stack[2].m_obj;
lean_object* v_a_249_ = stack[3].m_obj;
lean_object* v_a_250_ = stack[4].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_Lean_Parser_levelParser_parenthesizer(v_rbp_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_parenthesizer___boxed(lean_object* v_rbp_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Parser_levelParser_parenthesizer(v_rbp_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
return v_res_261_;
}
}
lean_object* l_Lean_Parser_Level_paren_parenthesizer(lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((lean_object*)(l_Lean_Parser_Level_paren_parenthesizer___closed__0));
v___x_293_ = ((lean_object*)(l_Lean_Parser_Level_paren_parenthesizer___closed__7));
v___x_294_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_292_, v___x_293_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_294_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_paren_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_287_ = stack[0].m_obj;
lean_object* v_a_288_ = stack[1].m_obj;
lean_object* v_a_289_ = stack[2].m_obj;
lean_object* v_a_290_ = stack[3].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_Parser_Level_paren_parenthesizer(v_a_287_, v_a_288_, v_a_289_, v_a_290_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_parenthesizer___boxed(lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Parser_Level_paren_parenthesizer(v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_301_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15(){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_311_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_312_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1));
v___x_313_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_paren_parenthesizer___boxed), 5, 0);
v___x_314_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_310_, v___x_311_, v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_315_;
v_res_315_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___boxed(lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
return v_res_317_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__2(void){
_start:
{
uint8_t v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = 0;
v___x_325_ = 1;
v___x_326_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_327_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__0));
v___x_328_ = l_Lean_Parser_mkAntiquot(v___x_327_, v___x_326_, v___x_325_, v___x_324_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__3(void){
_start:
{
uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = 1;
v___x_330_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__0));
v___x_331_ = l_Lean_Parser_nonReservedSymbol(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__4(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Lean_Parser_maxPrec;
v___x_333_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_334_ = l_Lean_Parser_categoryParser(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__5(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__4, &l_Lean_Parser_Level_max___closed__4_once, _init_l_Lean_Parser_Level_max___closed__4);
v___x_336_ = l_Lean_Parser_skip;
v___x_337_ = l_Lean_Parser_andthen(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__6(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__5, &l_Lean_Parser_Level_max___closed__5_once, _init_l_Lean_Parser_Level_max___closed__5);
v___x_339_ = l_Lean_Parser_many1(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__7(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__6, &l_Lean_Parser_Level_max___closed__6_once, _init_l_Lean_Parser_Level_max___closed__6);
v___x_341_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__3, &l_Lean_Parser_Level_max___closed__3_once, _init_l_Lean_Parser_Level_max___closed__3);
v___x_342_ = l_Lean_Parser_andthen(v___x_341_, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__8(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__7, &l_Lean_Parser_Level_max___closed__7_once, _init_l_Lean_Parser_Level_max___closed__7);
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_346_ = l_Lean_Parser_leadingNode(v___x_345_, v___x_344_, v___x_343_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__9(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__8, &l_Lean_Parser_Level_max___closed__8_once, _init_l_Lean_Parser_Level_max___closed__8);
v___x_348_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__2, &l_Lean_Parser_Level_max___closed__2_once, _init_l_Lean_Parser_Level_max___closed__2);
v___x_349_ = l_Lean_Parser_withAntiquot(v___x_348_, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__10(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__9, &l_Lean_Parser_Level_max___closed__9_once, _init_l_Lean_Parser_Level_max___closed__9);
v___x_351_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_352_ = l_Lean_Parser_withCache(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__10, &l_Lean_Parser_Level_max___closed__10_once, _init_l_Lean_Parser_Level_max___closed__10);
return v___x_353_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1(){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_356_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_357_ = l_Lean_Parser_Level_max;
v___x_358_ = lean_unsigned_to_nat(1000u);
v___x_359_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_355_, v___x_356_, v___x_357_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_360_;
v_res_360_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1___boxed(lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
return v_res_362_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3(){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_390_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6));
v___x_391_ = l_Lean_addBuiltinDeclarationRanges(v___x_389_, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_392_;
v_res_392_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___boxed(lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
return v_res_394_;
}
}
lean_object* l_Lean_Parser_Level_max_formatter___lam__0(lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_396_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_max_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_395_ = stack[0].m_obj;
lean_object* v___y_396_ = stack[1].m_obj;
lean_object* v___y_397_ = stack[2].m_obj;
lean_object* v___y_398_ = stack[3].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_Parser_Level_max_formatter___lam__0(v___y_395_, v___y_396_, v___y_397_, v___y_398_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___lam__0___boxed(lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Parser_Level_max_formatter___lam__0(v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = l_Lean_Parser_maxPrec;
v___x_421_ = lean_alloc_closure((void*)(l_Lean_Parser_levelParser_formatter___boxed), 6, 1);
lean_closure_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__4(void){
_start:
{
lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__3, &l_Lean_Parser_Level_max_formatter___closed__3_once, _init_l_Lean_Parser_Level_max_formatter___closed__3);
v___f_423_ = ((lean_object*)(l_Lean_Parser_Level_max_formatter___closed__0));
v___x_424_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_424_, 0, v___f_423_);
lean_closure_set(v___x_424_, 1, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__5(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__4, &l_Lean_Parser_Level_max_formatter___closed__4_once, _init_l_Lean_Parser_Level_max_formatter___closed__4);
v___x_426_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter___boxed), 6, 1);
lean_closure_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__6(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__5, &l_Lean_Parser_Level_max_formatter___closed__5_once, _init_l_Lean_Parser_Level_max_formatter___closed__5);
v___x_428_ = ((lean_object*)(l_Lean_Parser_Level_max_formatter___closed__2));
v___x_429_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_429_, 0, v___x_428_);
lean_closure_set(v___x_429_, 1, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__7(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_430_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__6, &l_Lean_Parser_Level_max_formatter___closed__6_once, _init_l_Lean_Parser_Level_max_formatter___closed__6);
v___x_431_ = lean_unsigned_to_nat(1024u);
v___x_432_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_433_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_433_, 0, v___x_432_);
lean_closure_set(v___x_433_, 1, v___x_431_);
lean_closure_set(v___x_433_, 2, v___x_430_);
return v___x_433_;
}
}
lean_object* l_Lean_Parser_Level_max_formatter(lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((lean_object*)(l_Lean_Parser_Level_max_formatter___closed__1));
v___x_440_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__7, &l_Lean_Parser_Level_max_formatter___closed__7_once, _init_l_Lean_Parser_Level_max_formatter___closed__7);
v___x_441_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_439_, v___x_440_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
return v___x_441_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_max_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_434_ = stack[0].m_obj;
lean_object* v_a_435_ = stack[1].m_obj;
lean_object* v_a_436_ = stack[2].m_obj;
lean_object* v_a_437_ = stack[3].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_Lean_Parser_Level_max_formatter(v_a_434_, v_a_435_, v_a_436_, v_a_437_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___boxed(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Parser_Level_max_formatter(v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_448_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7(){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_457_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_458_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0));
v___x_459_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_max_formatter___boxed), 5, 0);
v___x_460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_456_, v___x_457_, v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
return v_res_463_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = l_Lean_Parser_maxPrec;
v___x_477_ = lean_alloc_closure((void*)(l_Lean_Parser_levelParser_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__3, &l_Lean_Parser_Level_max_parenthesizer___closed__3_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__3);
v___x_479_ = ((lean_object*)(l_Lean_Parser_Level_max_parenthesizer___closed__2));
v___x_480_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_480_, 0, v___x_479_);
lean_closure_set(v___x_480_, 1, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__4, &l_Lean_Parser_Level_max_parenthesizer___closed__4_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__4);
v___x_482_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__5, &l_Lean_Parser_Level_max_parenthesizer___closed__5_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__5);
v___x_484_ = ((lean_object*)(l_Lean_Parser_Level_max_parenthesizer___closed__1));
v___x_485_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_485_, 0, v___x_484_);
lean_closure_set(v___x_485_, 1, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__6, &l_Lean_Parser_Level_max_parenthesizer___closed__6_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__6);
v___x_487_ = lean_unsigned_to_nat(1024u);
v___x_488_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_489_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_489_, 0, v___x_488_);
lean_closure_set(v___x_489_, 1, v___x_487_);
lean_closure_set(v___x_489_, 2, v___x_486_);
return v___x_489_;
}
}
lean_object* l_Lean_Parser_Level_max_parenthesizer(lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l_Lean_Parser_Level_max_parenthesizer___closed__0));
v___x_496_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__7, &l_Lean_Parser_Level_max_parenthesizer___closed__7_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__7);
v___x_497_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_495_, v___x_496_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_497_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_max_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_490_ = stack[0].m_obj;
lean_object* v_a_491_ = stack[1].m_obj;
lean_object* v_a_492_ = stack[2].m_obj;
lean_object* v_a_493_ = stack[3].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Parser_Level_max_parenthesizer(v_a_490_, v_a_491_, v_a_492_, v_a_493_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_parenthesizer___boxed(lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Parser_Level_max_parenthesizer(v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_504_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11(){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_513_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_514_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0));
v___x_515_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_max_parenthesizer___boxed), 5, 0);
v___x_516_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_512_, v___x_513_, v___x_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_517_;
v_res_517_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___boxed(lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__2(void){
_start:
{
uint8_t v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = 0;
v___x_527_ = 1;
v___x_528_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_529_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__0));
v___x_530_ = l_Lean_Parser_mkAntiquot(v___x_529_, v___x_528_, v___x_527_, v___x_526_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__3(void){
_start:
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = 1;
v___x_532_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__0));
v___x_533_ = l_Lean_Parser_nonReservedSymbol(v___x_532_, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__4(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__6, &l_Lean_Parser_Level_max___closed__6_once, _init_l_Lean_Parser_Level_max___closed__6);
v___x_535_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__3, &l_Lean_Parser_Level_imax___closed__3_once, _init_l_Lean_Parser_Level_imax___closed__3);
v___x_536_ = l_Lean_Parser_andthen(v___x_535_, v___x_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__5(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__4, &l_Lean_Parser_Level_imax___closed__4_once, _init_l_Lean_Parser_Level_imax___closed__4);
v___x_538_ = lean_unsigned_to_nat(1024u);
v___x_539_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_540_ = l_Lean_Parser_leadingNode(v___x_539_, v___x_538_, v___x_537_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__6(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__5, &l_Lean_Parser_Level_imax___closed__5_once, _init_l_Lean_Parser_Level_imax___closed__5);
v___x_542_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__2, &l_Lean_Parser_Level_imax___closed__2_once, _init_l_Lean_Parser_Level_imax___closed__2);
v___x_543_ = l_Lean_Parser_withAntiquot(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__7(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__6, &l_Lean_Parser_Level_imax___closed__6_once, _init_l_Lean_Parser_Level_imax___closed__6);
v___x_545_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_546_ = l_Lean_Parser_withCache(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__7, &l_Lean_Parser_Level_imax___closed__7_once, _init_l_Lean_Parser_Level_imax___closed__7);
return v___x_547_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1(){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_549_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_550_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_551_ = l_Lean_Parser_Level_imax;
v___x_552_ = lean_unsigned_to_nat(1000u);
v___x_553_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_549_, v___x_550_, v___x_551_, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_554_;
v_res_554_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1___boxed(lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
return v_res_556_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3(){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_583_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6));
v___x_584_ = l_Lean_addBuiltinDeclarationRanges(v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_585_;
v_res_585_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___boxed(lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
return v_res_587_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_formatter___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__5, &l_Lean_Parser_Level_max_formatter___closed__5_once, _init_l_Lean_Parser_Level_max_formatter___closed__5);
v___x_600_ = ((lean_object*)(l_Lean_Parser_Level_imax_formatter___closed__1));
v___x_601_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_601_, 0, v___x_600_);
lean_closure_set(v___x_601_, 1, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_formatter___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_obj_once(&l_Lean_Parser_Level_imax_formatter___closed__2, &l_Lean_Parser_Level_imax_formatter___closed__2_once, _init_l_Lean_Parser_Level_imax_formatter___closed__2);
v___x_603_ = lean_unsigned_to_nat(1024u);
v___x_604_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_605_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_605_, 0, v___x_604_);
lean_closure_set(v___x_605_, 1, v___x_603_);
lean_closure_set(v___x_605_, 2, v___x_602_);
return v___x_605_;
}
}
lean_object* l_Lean_Parser_Level_imax_formatter(lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l_Lean_Parser_Level_imax_formatter___closed__0));
v___x_612_ = lean_obj_once(&l_Lean_Parser_Level_imax_formatter___closed__3, &l_Lean_Parser_Level_imax_formatter___closed__3_once, _init_l_Lean_Parser_Level_imax_formatter___closed__3);
v___x_613_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_611_, v___x_612_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_613_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_imax_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_606_ = stack[0].m_obj;
lean_object* v_a_607_ = stack[1].m_obj;
lean_object* v_a_608_ = stack[2].m_obj;
lean_object* v_a_609_ = stack[3].m_obj;
lean_object* v_res_614_;
v_res_614_ = l_Lean_Parser_Level_imax_formatter(v_a_606_, v_a_607_, v_a_608_, v_a_609_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_formatter___boxed(lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Parser_Level_imax_formatter(v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
return v_res_620_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7(){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_629_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_630_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0));
v___x_631_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_imax_formatter___boxed), 5, 0);
v___x_632_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_628_, v___x_629_, v___x_630_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_633_;
v_res_633_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___boxed(lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
return v_res_635_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__5, &l_Lean_Parser_Level_max_parenthesizer___closed__5_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__5);
v___x_648_ = ((lean_object*)(l_Lean_Parser_Level_imax_parenthesizer___closed__1));
v___x_649_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_649_, 0, v___x_648_);
lean_closure_set(v___x_649_, 1, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_obj_once(&l_Lean_Parser_Level_imax_parenthesizer___closed__2, &l_Lean_Parser_Level_imax_parenthesizer___closed__2_once, _init_l_Lean_Parser_Level_imax_parenthesizer___closed__2);
v___x_651_ = lean_unsigned_to_nat(1024u);
v___x_652_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_653_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_653_, 0, v___x_652_);
lean_closure_set(v___x_653_, 1, v___x_651_);
lean_closure_set(v___x_653_, 2, v___x_650_);
return v___x_653_;
}
}
lean_object* l_Lean_Parser_Level_imax_parenthesizer(lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((lean_object*)(l_Lean_Parser_Level_imax_parenthesizer___closed__0));
v___x_660_ = lean_obj_once(&l_Lean_Parser_Level_imax_parenthesizer___closed__3, &l_Lean_Parser_Level_imax_parenthesizer___closed__3_once, _init_l_Lean_Parser_Level_imax_parenthesizer___closed__3);
v___x_661_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_659_, v___x_660_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_661_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_imax_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_654_ = stack[0].m_obj;
lean_object* v_a_655_ = stack[1].m_obj;
lean_object* v_a_656_ = stack[2].m_obj;
lean_object* v_a_657_ = stack[3].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_Parser_Level_imax_parenthesizer(v_a_654_, v_a_655_, v_a_656_, v_a_657_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_parenthesizer___boxed(lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Parser_Level_imax_parenthesizer(v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_668_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11(){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_677_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_678_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0));
v___x_679_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_imax_parenthesizer___boxed), 5, 0);
v___x_680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_676_, v___x_677_, v___x_678_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_681_;
v_res_681_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___boxed(lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
return v_res_683_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__2(void){
_start:
{
uint8_t v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_690_ = 0;
v___x_691_ = 1;
v___x_692_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_693_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__0));
v___x_694_ = l_Lean_Parser_mkAntiquot(v___x_693_, v___x_692_, v___x_691_, v___x_690_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__4(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__3));
v___x_697_ = l_Lean_Parser_symbol(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__5(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__4, &l_Lean_Parser_Level_hole___closed__4_once, _init_l_Lean_Parser_Level_hole___closed__4);
v___x_699_ = lean_unsigned_to_nat(1024u);
v___x_700_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_701_ = l_Lean_Parser_leadingNode(v___x_700_, v___x_699_, v___x_698_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__6(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__5, &l_Lean_Parser_Level_hole___closed__5_once, _init_l_Lean_Parser_Level_hole___closed__5);
v___x_703_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__2, &l_Lean_Parser_Level_hole___closed__2_once, _init_l_Lean_Parser_Level_hole___closed__2);
v___x_704_ = l_Lean_Parser_withAntiquot(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__7(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__6, &l_Lean_Parser_Level_hole___closed__6_once, _init_l_Lean_Parser_Level_hole___closed__6);
v___x_706_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_707_ = l_Lean_Parser_withCache(v___x_706_, v___x_705_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole(void){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__7, &l_Lean_Parser_Level_hole___closed__7_once, _init_l_Lean_Parser_Level_hole___closed__7);
return v___x_708_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1(){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_710_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_711_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_712_ = l_Lean_Parser_Level_hole;
v___x_713_ = lean_unsigned_to_nat(1000u);
v___x_714_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_710_, v___x_711_, v___x_712_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_715_;
v_res_715_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1___boxed(lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
return v_res_717_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3(){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_745_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6));
v___x_746_ = l_Lean_addBuiltinDeclarationRanges(v___x_744_, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_747_;
v_res_747_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___boxed(lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
return v_res_749_;
}
}
lean_object* l_Lean_Parser_Level_hole_formatter(lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = ((lean_object*)(l_Lean_Parser_Level_hole_formatter___closed__0));
v___x_769_ = ((lean_object*)(l_Lean_Parser_Level_hole_formatter___closed__2));
v___x_770_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_768_, v___x_769_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
return v___x_770_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_hole_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_763_ = stack[0].m_obj;
lean_object* v_a_764_ = stack[1].m_obj;
lean_object* v_a_765_ = stack[2].m_obj;
lean_object* v_a_766_ = stack[3].m_obj;
lean_object* v_res_771_;
v_res_771_ = l_Lean_Parser_Level_hole_formatter(v_a_763_, v_a_764_, v_a_765_, v_a_766_);
stack->m_obj
 = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_formatter___boxed(lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Parser_Level_hole_formatter(v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_777_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7(){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_785_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_786_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_787_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0));
v___x_788_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_hole_formatter___boxed), 5, 0);
v___x_789_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_785_, v___x_786_, v___x_787_, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_790_;
v_res_790_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___boxed(lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
return v_res_792_;
}
}
lean_object* l_Lean_Parser_Level_hole_parenthesizer(lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((lean_object*)(l_Lean_Parser_Level_hole_parenthesizer___closed__0));
v___x_812_ = ((lean_object*)(l_Lean_Parser_Level_hole_parenthesizer___closed__2));
v___x_813_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_811_, v___x_812_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_813_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_hole_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_806_ = stack[0].m_obj;
lean_object* v_a_807_ = stack[1].m_obj;
lean_object* v_a_808_ = stack[2].m_obj;
lean_object* v_a_809_ = stack[3].m_obj;
lean_object* v_res_814_;
v_res_814_ = l_Lean_Parser_Level_hole_parenthesizer(v_a_806_, v_a_807_, v_a_808_, v_a_809_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_parenthesizer___boxed(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Parser_Level_hole_parenthesizer(v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11(){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_828_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_829_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_830_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0));
v___x_831_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_hole_parenthesizer___boxed), 5, 0);
v___x_832_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_828_, v___x_829_, v___x_830_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_833_;
v_res_833_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___boxed(lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
return v_res_835_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num___closed__0(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = l_Lean_Parser_maxPrec;
v___x_837_ = l_Lean_Parser_checkPrec(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num___closed__1(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = l_Lean_Parser_numLit;
v___x_839_ = lean_obj_once(&l_Lean_Parser_Level_num___closed__0, &l_Lean_Parser_Level_num___closed__0_once, _init_l_Lean_Parser_Level_num___closed__0);
v___x_840_ = l_Lean_Parser_andthen(v___x_839_, v___x_838_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num(void){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lean_Parser_Level_num___closed__1, &l_Lean_Parser_Level_num___closed__1_once, _init_l_Lean_Parser_Level_num___closed__1);
return v___x_841_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1(){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_849_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_850_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1));
v___x_851_ = l_Lean_Parser_Level_num;
v___x_852_ = lean_unsigned_to_nat(1000u);
v___x_853_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_849_, v___x_850_, v___x_851_, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_854_;
v_res_854_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___boxed(lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
return v_res_856_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3(){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1));
v___x_882_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6));
v___x_883_ = l_Lean_addBuiltinDeclarationRanges(v___x_881_, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_884_;
v_res_884_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___boxed(lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
return v_res_886_;
}
}
lean_object* l_Lean_Parser_Level_num_formatter(lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
v___x_894_ = ((lean_object*)(l_Lean_Parser_Level_num_formatter___closed__0));
v___x_895_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_893_, v___x_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_895_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_num_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_888_ = stack[0].m_obj;
lean_object* v_a_889_ = stack[1].m_obj;
lean_object* v_a_890_ = stack[2].m_obj;
lean_object* v_a_891_ = stack[3].m_obj;
lean_object* v_res_896_;
v_res_896_ = l_Lean_Parser_Level_num_formatter(v_a_888_, v_a_889_, v_a_890_, v_a_891_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_formatter___boxed(lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Parser_Level_num_formatter(v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
return v_res_902_;
}
}
lean_object* l_Lean_Parser_Level_num_parenthesizer___lam__0(lean_object* v___x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(v___x_903_, v___y_905_);
return v___x_909_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_num_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_903_ = stack[0].m_obj;
lean_object* v___y_904_ = stack[1].m_obj;
lean_object* v___y_905_ = stack[2].m_obj;
lean_object* v___y_906_ = stack[3].m_obj;
lean_object* v___y_907_ = stack[4].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_Parser_Level_num_parenthesizer___lam__0(v___x_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed(lean_object* v___x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Parser_Level_num_parenthesizer___lam__0(v___x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_918_; lean_object* v___f_919_; 
v___x_918_ = l_Lean_Parser_maxPrec;
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_919_, 0, v___x_918_);
return v___f_919_;
}
}
lean_object* l_Lean_Parser_Level_num_parenthesizer(lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___f_926_ = lean_obj_once(&l_Lean_Parser_Level_num_parenthesizer___closed__0, &l_Lean_Parser_Level_num_parenthesizer___closed__0_once, _init_l_Lean_Parser_Level_num_parenthesizer___closed__0);
v___x_927_ = ((lean_object*)(l_Lean_Parser_Level_num_parenthesizer___closed__1));
v___x_928_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___f_926_, v___x_927_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
return v___x_928_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_num_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_921_ = stack[0].m_obj;
lean_object* v_a_922_ = stack[1].m_obj;
lean_object* v_a_923_ = stack[2].m_obj;
lean_object* v_a_924_ = stack[3].m_obj;
lean_object* v_res_929_;
v_res_929_ = l_Lean_Parser_Level_num_parenthesizer(v_a_921_, v_a_922_, v_a_923_, v_a_924_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___boxed(lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Parser_Level_num_parenthesizer(v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_Parser_Level_ident___closed__0(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Parser_ident;
v___x_937_ = lean_obj_once(&l_Lean_Parser_Level_num___closed__0, &l_Lean_Parser_Level_num___closed__0_once, _init_l_Lean_Parser_Level_num___closed__0);
v___x_938_ = l_Lean_Parser_andthen(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Parser_Level_ident(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_obj_once(&l_Lean_Parser_Level_ident___closed__0, &l_Lean_Parser_Level_ident___closed__0_once, _init_l_Lean_Parser_Level_ident___closed__0);
return v___x_939_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1(){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_947_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_948_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1));
v___x_949_ = l_Lean_Parser_Level_ident;
v___x_950_ = lean_unsigned_to_nat(1000u);
v___x_951_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_947_, v___x_948_, v___x_949_, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_952_;
v_res_952_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___boxed(lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
return v_res_954_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3(){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1));
v___x_982_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6));
v___x_983_ = l_Lean_addBuiltinDeclarationRanges(v___x_981_, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_984_;
v_res_984_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
stack->m_obj
 = v_res_984_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___boxed(lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
return v_res_986_;
}
}
lean_object* l_Lean_Parser_Level_ident_formatter(lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
v___x_994_ = ((lean_object*)(l_Lean_Parser_Level_ident_formatter___closed__0));
v___x_995_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_993_, v___x_994_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_995_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_ident_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_988_ = stack[0].m_obj;
lean_object* v_a_989_ = stack[1].m_obj;
lean_object* v_a_990_ = stack[2].m_obj;
lean_object* v_a_991_ = stack[3].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_Parser_Level_ident_formatter(v_a_988_, v_a_989_, v_a_990_, v_a_991_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_formatter___boxed(lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Parser_Level_ident_formatter(v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
return v_res_1002_;
}
}
lean_object* l_Lean_Parser_Level_ident_parenthesizer(lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___f_1009_ = lean_obj_once(&l_Lean_Parser_Level_num_parenthesizer___closed__0, &l_Lean_Parser_Level_num_parenthesizer___closed__0_once, _init_l_Lean_Parser_Level_num_parenthesizer___closed__0);
v___x_1010_ = ((lean_object*)(l_Lean_Parser_Level_ident_parenthesizer___closed__0));
v___x_1011_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___f_1009_, v___x_1010_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1011_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_ident_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1004_ = stack[0].m_obj;
lean_object* v_a_1005_ = stack[1].m_obj;
lean_object* v_a_1006_ = stack[2].m_obj;
lean_object* v_a_1007_ = stack[3].m_obj;
lean_object* v_res_1012_;
v_res_1012_ = l_Lean_Parser_Level_ident_parenthesizer(v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
stack->m_obj
 = v_res_1012_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_parenthesizer___boxed(lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Parser_Level_ident_parenthesizer(v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1018_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit___closed__3(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__2));
v___x_1027_ = l_Lean_Parser_symbol(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit___closed__4(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lean_Parser_numLit;
v___x_1029_ = lean_obj_once(&l_Lean_Parser_Level_addLit___closed__3, &l_Lean_Parser_Level_addLit___closed__3_once, _init_l_Lean_Parser_Level_addLit___closed__3);
v___x_1030_ = l_Lean_Parser_andthen(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit___closed__5(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1031_ = lean_obj_once(&l_Lean_Parser_Level_addLit___closed__4, &l_Lean_Parser_Level_addLit___closed__4_once, _init_l_Lean_Parser_Level_addLit___closed__4);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_unsigned_to_nat(65u);
v___x_1034_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1035_ = l_Lean_Parser_trailingNode(v___x_1034_, v___x_1033_, v___x_1032_, v___x_1031_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Lean_Parser_Level_addLit___closed__5, &l_Lean_Parser_Level_addLit___closed__5_once, _init_l_Lean_Parser_Level_addLit___closed__5);
return v___x_1036_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1(){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1038_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_1039_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1040_ = l_Lean_Parser_Level_addLit;
v___x_1041_ = lean_unsigned_to_nat(1000u);
v___x_1042_ = l_Lean_Parser_addBuiltinTrailingParser(v___x_1038_, v___x_1039_, v___x_1040_, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1043_;
v_res_1043_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1___boxed(lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
return v_res_1045_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3(){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1073_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6));
v___x_1074_ = l_Lean_addBuiltinDeclarationRanges(v___x_1072_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1075_;
v_res_1075_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___boxed(lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
return v_res_1077_;
}
}
lean_object* l_Lean_Parser_Level_addLit_formatter(lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1089_ = ((lean_object*)(l_Lean_Parser_Level_addLit_formatter___closed__1));
v___x_1090_ = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(v___x_1088_, v___x_1089_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_addLit_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1083_ = stack[0].m_obj;
lean_object* v_a_1084_ = stack[1].m_obj;
lean_object* v_a_1085_ = stack[2].m_obj;
lean_object* v_a_1086_ = stack[3].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Lean_Parser_Level_addLit_formatter(v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_formatter___boxed(lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Parser_Level_addLit_formatter(v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
return v_res_1097_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7(){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1105_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1106_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1107_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0));
v___x_1108_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_addLit_formatter___boxed), 5, 0);
v___x_1109_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1105_, v___x_1106_, v___x_1107_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1110_;
v_res_1110_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___boxed(lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
return v_res_1112_;
}
}
lean_object* l_Lean_Parser_Level_addLit_parenthesizer(lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1123_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1124_ = lean_unsigned_to_nat(65u);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = ((lean_object*)(l_Lean_Parser_Level_addLit_parenthesizer___closed__1));
v___x_1127_ = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(v___x_1123_, v___x_1124_, v___x_1125_, v___x_1126_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1127_;
}
}
LEAN_EXPORT void l_Lean_Parser_Level_addLit_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1118_ = stack[0].m_obj;
lean_object* v_a_1119_ = stack[1].m_obj;
lean_object* v_a_1120_ = stack[2].m_obj;
lean_object* v_a_1121_ = stack[3].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l_Lean_Parser_Level_addLit_parenthesizer(v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_parenthesizer___boxed(lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Parser_Level_addLit_parenthesizer(v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1134_;
}
}
lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11(){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1142_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1143_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1144_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0));
v___x_1145_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_addLit_parenthesizer___boxed), 5, 0);
v___x_1146_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1142_, v___x_1143_, v___x_1144_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1147_;
v_res_1147_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___boxed(lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
return v_res_1149_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
lean_mark_persistent(l_Lean_Parser_Level_paren);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_max = _init_l_Lean_Parser_Level_max();
lean_mark_persistent(l_Lean_Parser_Level_max);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_imax = _init_l_Lean_Parser_Level_imax();
lean_mark_persistent(l_Lean_Parser_Level_imax);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_hole = _init_l_Lean_Parser_Level_hole();
lean_mark_persistent(l_Lean_Parser_Level_hole);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_num = _init_l_Lean_Parser_Level_num();
lean_mark_persistent(l_Lean_Parser_Level_num);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_ident = _init_l_Lean_Parser_Level_ident();
lean_mark_persistent(l_Lean_Parser_Level_ident);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
lean_mark_persistent(l_Lean_Parser_Level_addLit);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Level(builtin);
}
#ifdef __cplusplus
}
#endif
