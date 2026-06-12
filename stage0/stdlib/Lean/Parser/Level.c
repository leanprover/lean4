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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2____boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser(lean_object* v_rbp_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_79_ = l_Lean_Parser_categoryParser(v___x_78_, v_rbp_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__2(void){
_start:
{
uint8_t v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = 0;
v___x_87_ = 1;
v___x_88_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_89_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__0));
v___x_90_ = l_Lean_Parser_mkAntiquot(v___x_89_, v___x_88_, v___x_87_, v___x_86_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__4(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__3));
v___x_93_ = l_Lean_Parser_symbol(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__5(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_96_ = l_Lean_Parser_categoryParser(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__6(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__5, &l_Lean_Parser_Level_paren___closed__5_once, _init_l_Lean_Parser_Level_paren___closed__5);
v___x_98_ = l_Lean_Parser_withoutPosition(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__8(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__7));
v___x_101_ = l_Lean_Parser_symbol(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__9(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__8, &l_Lean_Parser_Level_paren___closed__8_once, _init_l_Lean_Parser_Level_paren___closed__8);
v___x_103_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__6, &l_Lean_Parser_Level_paren___closed__6_once, _init_l_Lean_Parser_Level_paren___closed__6);
v___x_104_ = l_Lean_Parser_andthen(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__10(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__9, &l_Lean_Parser_Level_paren___closed__9_once, _init_l_Lean_Parser_Level_paren___closed__9);
v___x_106_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__4, &l_Lean_Parser_Level_paren___closed__4_once, _init_l_Lean_Parser_Level_paren___closed__4);
v___x_107_ = l_Lean_Parser_andthen(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__11(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__10, &l_Lean_Parser_Level_paren___closed__10_once, _init_l_Lean_Parser_Level_paren___closed__10);
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_111_ = l_Lean_Parser_leadingNode(v___x_110_, v___x_109_, v___x_108_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__12(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__11, &l_Lean_Parser_Level_paren___closed__11_once, _init_l_Lean_Parser_Level_paren___closed__11);
v___x_113_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__2, &l_Lean_Parser_Level_paren___closed__2_once, _init_l_Lean_Parser_Level_paren___closed__2);
v___x_114_ = l_Lean_Parser_withAntiquot(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren___closed__13(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__12, &l_Lean_Parser_Level_paren___closed__12_once, _init_l_Lean_Parser_Level_paren___closed__12);
v___x_116_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_117_ = l_Lean_Parser_withCache(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Parser_Level_paren(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Parser_Level_paren___closed__13, &l_Lean_Parser_Level_paren___closed__13_once, _init_l_Lean_Parser_Level_paren___closed__13);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1(){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_121_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_122_ = l_Lean_Parser_Level_paren;
v___x_123_ = lean_unsigned_to_nat(1000u);
v___x_124_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_120_, v___x_121_, v___x_122_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1___boxed(lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3(){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_154_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6));
v___x_155_ = l_Lean_addBuiltinDeclarationRanges(v___x_153_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___boxed(lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___redArg(lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_164_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_163_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___redArg___boxed(lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Parser_levelParser_formatter___redArg(v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter(lean_object* v_rbp_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Parser_levelParser_formatter___redArg(v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_formatter___boxed(lean_object* v_rbp_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Parser_levelParser_formatter(v_rbp_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_rbp_178_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_formatter(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((lean_object*)(l_Lean_Parser_Level_paren_formatter___closed__0));
v___x_216_ = ((lean_object*)(l_Lean_Parser_Level_paren_formatter___closed__7));
v___x_217_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_215_, v___x_216_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_formatter___boxed(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Parser_Level_paren_formatter(v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9(){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_233_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_234_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1));
v___x_235_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_paren_formatter___boxed), 5, 0);
v___x_236_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_232_, v___x_233_, v___x_234_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___boxed(lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_parenthesizer(lean_object* v_rbp_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_246_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_245_, v_rbp_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_levelParser_parenthesizer___boxed(lean_object* v_rbp_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Parser_levelParser_parenthesizer(v_rbp_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_parenthesizer(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lean_Parser_Level_paren_parenthesizer___closed__0));
v___x_285_ = ((lean_object*)(l_Lean_Parser_Level_paren_parenthesizer___closed__7));
v___x_286_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_284_, v___x_285_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_paren_parenthesizer___boxed(lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Parser_Level_paren_parenthesizer(v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15(){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_301_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_302_ = ((lean_object*)(l_Lean_Parser_Level_paren___closed__1));
v___x_303_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1));
v___x_304_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_paren_parenthesizer___boxed), 5, 0);
v___x_305_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_301_, v___x_302_, v___x_303_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___boxed(lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
return v_res_307_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__2(void){
_start:
{
uint8_t v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = 0;
v___x_315_ = 1;
v___x_316_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_317_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__0));
v___x_318_ = l_Lean_Parser_mkAntiquot(v___x_317_, v___x_316_, v___x_315_, v___x_314_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__3(void){
_start:
{
uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = 1;
v___x_320_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__0));
v___x_321_ = l_Lean_Parser_nonReservedSymbol(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__4(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = l_Lean_Parser_maxPrec;
v___x_323_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_324_ = l_Lean_Parser_categoryParser(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__5(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__4, &l_Lean_Parser_Level_max___closed__4_once, _init_l_Lean_Parser_Level_max___closed__4);
v___x_326_ = l_Lean_Parser_skip;
v___x_327_ = l_Lean_Parser_andthen(v___x_326_, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__6(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__5, &l_Lean_Parser_Level_max___closed__5_once, _init_l_Lean_Parser_Level_max___closed__5);
v___x_329_ = l_Lean_Parser_many1(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__7(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__6, &l_Lean_Parser_Level_max___closed__6_once, _init_l_Lean_Parser_Level_max___closed__6);
v___x_331_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__3, &l_Lean_Parser_Level_max___closed__3_once, _init_l_Lean_Parser_Level_max___closed__3);
v___x_332_ = l_Lean_Parser_andthen(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__8(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_333_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__7, &l_Lean_Parser_Level_max___closed__7_once, _init_l_Lean_Parser_Level_max___closed__7);
v___x_334_ = lean_unsigned_to_nat(1024u);
v___x_335_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_336_ = l_Lean_Parser_leadingNode(v___x_335_, v___x_334_, v___x_333_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__9(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__8, &l_Lean_Parser_Level_max___closed__8_once, _init_l_Lean_Parser_Level_max___closed__8);
v___x_338_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__2, &l_Lean_Parser_Level_max___closed__2_once, _init_l_Lean_Parser_Level_max___closed__2);
v___x_339_ = l_Lean_Parser_withAntiquot(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max___closed__10(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__9, &l_Lean_Parser_Level_max___closed__9_once, _init_l_Lean_Parser_Level_max___closed__9);
v___x_341_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_342_ = l_Lean_Parser_withCache(v___x_341_, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__10, &l_Lean_Parser_Level_max___closed__10_once, _init_l_Lean_Parser_Level_max___closed__10);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1(){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_345_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_346_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_347_ = l_Lean_Parser_Level_max;
v___x_348_ = lean_unsigned_to_nat(1000u);
v___x_349_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_345_, v___x_346_, v___x_347_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1___boxed(lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3(){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_379_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6));
v___x_380_ = l_Lean_addBuiltinDeclarationRanges(v___x_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___boxed(lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___lam__0(lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___lam__0___boxed(lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Parser_Level_max_formatter___lam__0(v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__3(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = l_Lean_Parser_maxPrec;
v___x_408_ = lean_alloc_closure((void*)(l_Lean_Parser_levelParser_formatter___boxed), 6, 1);
lean_closure_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__4(void){
_start:
{
lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v___x_409_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__3, &l_Lean_Parser_Level_max_formatter___closed__3_once, _init_l_Lean_Parser_Level_max_formatter___closed__3);
v___f_410_ = ((lean_object*)(l_Lean_Parser_Level_max_formatter___closed__0));
v___x_411_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_411_, 0, v___f_410_);
lean_closure_set(v___x_411_, 1, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__5(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__4, &l_Lean_Parser_Level_max_formatter___closed__4_once, _init_l_Lean_Parser_Level_max_formatter___closed__4);
v___x_413_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter___boxed), 6, 1);
lean_closure_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__6(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__5, &l_Lean_Parser_Level_max_formatter___closed__5_once, _init_l_Lean_Parser_Level_max_formatter___closed__5);
v___x_415_ = ((lean_object*)(l_Lean_Parser_Level_max_formatter___closed__2));
v___x_416_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_416_, 0, v___x_415_);
lean_closure_set(v___x_416_, 1, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_formatter___closed__7(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__6, &l_Lean_Parser_Level_max_formatter___closed__6_once, _init_l_Lean_Parser_Level_max_formatter___closed__6);
v___x_418_ = lean_unsigned_to_nat(1024u);
v___x_419_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_420_, 0, v___x_419_);
lean_closure_set(v___x_420_, 1, v___x_418_);
lean_closure_set(v___x_420_, 2, v___x_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter(lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((lean_object*)(l_Lean_Parser_Level_max_formatter___closed__1));
v___x_427_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__7, &l_Lean_Parser_Level_max_formatter___closed__7_once, _init_l_Lean_Parser_Level_max_formatter___closed__7);
v___x_428_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_426_, v___x_427_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_formatter___boxed(lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Parser_Level_max_formatter(v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7(){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_443_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_444_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0));
v___x_445_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_max_formatter___boxed), 5, 0);
v___x_446_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_442_, v___x_443_, v___x_444_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___boxed(lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
return v_res_448_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = l_Lean_Parser_maxPrec;
v___x_462_ = lean_alloc_closure((void*)(l_Lean_Parser_levelParser_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__3, &l_Lean_Parser_Level_max_parenthesizer___closed__3_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__3);
v___x_464_ = ((lean_object*)(l_Lean_Parser_Level_max_parenthesizer___closed__2));
v___x_465_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_465_, 0, v___x_464_);
lean_closure_set(v___x_465_, 1, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__4, &l_Lean_Parser_Level_max_parenthesizer___closed__4_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__4);
v___x_467_ = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__5, &l_Lean_Parser_Level_max_parenthesizer___closed__5_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__5);
v___x_469_ = ((lean_object*)(l_Lean_Parser_Level_max_parenthesizer___closed__1));
v___x_470_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_470_, 0, v___x_469_);
lean_closure_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Parser_Level_max_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__6, &l_Lean_Parser_Level_max_parenthesizer___closed__6_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__6);
v___x_472_ = lean_unsigned_to_nat(1024u);
v___x_473_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_474_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_474_, 0, v___x_473_);
lean_closure_set(v___x_474_, 1, v___x_472_);
lean_closure_set(v___x_474_, 2, v___x_471_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_parenthesizer(lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(l_Lean_Parser_Level_max_parenthesizer___closed__0));
v___x_481_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__7, &l_Lean_Parser_Level_max_parenthesizer___closed__7_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__7);
v___x_482_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_480_, v___x_481_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_max_parenthesizer___boxed(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Parser_Level_max_parenthesizer(v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11(){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_496_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_497_ = ((lean_object*)(l_Lean_Parser_Level_max___closed__1));
v___x_498_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0));
v___x_499_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_max_parenthesizer___boxed), 5, 0);
v___x_500_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_496_, v___x_497_, v___x_498_, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___boxed(lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
return v_res_502_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__2(void){
_start:
{
uint8_t v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_509_ = 0;
v___x_510_ = 1;
v___x_511_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_512_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__0));
v___x_513_ = l_Lean_Parser_mkAntiquot(v___x_512_, v___x_511_, v___x_510_, v___x_509_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__3(void){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = 1;
v___x_515_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__0));
v___x_516_ = l_Lean_Parser_nonReservedSymbol(v___x_515_, v___x_514_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__4(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_obj_once(&l_Lean_Parser_Level_max___closed__6, &l_Lean_Parser_Level_max___closed__6_once, _init_l_Lean_Parser_Level_max___closed__6);
v___x_518_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__3, &l_Lean_Parser_Level_imax___closed__3_once, _init_l_Lean_Parser_Level_imax___closed__3);
v___x_519_ = l_Lean_Parser_andthen(v___x_518_, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__5(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__4, &l_Lean_Parser_Level_imax___closed__4_once, _init_l_Lean_Parser_Level_imax___closed__4);
v___x_521_ = lean_unsigned_to_nat(1024u);
v___x_522_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_523_ = l_Lean_Parser_leadingNode(v___x_522_, v___x_521_, v___x_520_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__6(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__5, &l_Lean_Parser_Level_imax___closed__5_once, _init_l_Lean_Parser_Level_imax___closed__5);
v___x_525_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__2, &l_Lean_Parser_Level_imax___closed__2_once, _init_l_Lean_Parser_Level_imax___closed__2);
v___x_526_ = l_Lean_Parser_withAntiquot(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax___closed__7(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__6, &l_Lean_Parser_Level_imax___closed__6_once, _init_l_Lean_Parser_Level_imax___closed__6);
v___x_528_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_529_ = l_Lean_Parser_withCache(v___x_528_, v___x_527_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lean_Parser_Level_imax___closed__7, &l_Lean_Parser_Level_imax___closed__7_once, _init_l_Lean_Parser_Level_imax___closed__7);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1(){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_533_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_534_ = l_Lean_Parser_Level_imax;
v___x_535_ = lean_unsigned_to_nat(1000u);
v___x_536_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_532_, v___x_533_, v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1___boxed(lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3(){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_565_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6));
v___x_566_ = l_Lean_addBuiltinDeclarationRanges(v___x_564_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___boxed(lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
return v_res_568_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_formatter___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_obj_once(&l_Lean_Parser_Level_max_formatter___closed__5, &l_Lean_Parser_Level_max_formatter___closed__5_once, _init_l_Lean_Parser_Level_max_formatter___closed__5);
v___x_581_ = ((lean_object*)(l_Lean_Parser_Level_imax_formatter___closed__1));
v___x_582_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_582_, 0, v___x_581_);
lean_closure_set(v___x_582_, 1, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_formatter___closed__3(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_obj_once(&l_Lean_Parser_Level_imax_formatter___closed__2, &l_Lean_Parser_Level_imax_formatter___closed__2_once, _init_l_Lean_Parser_Level_imax_formatter___closed__2);
v___x_584_ = lean_unsigned_to_nat(1024u);
v___x_585_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_586_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_586_, 0, v___x_585_);
lean_closure_set(v___x_586_, 1, v___x_584_);
lean_closure_set(v___x_586_, 2, v___x_583_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_formatter(lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((lean_object*)(l_Lean_Parser_Level_imax_formatter___closed__0));
v___x_593_ = lean_obj_once(&l_Lean_Parser_Level_imax_formatter___closed__3, &l_Lean_Parser_Level_imax_formatter___closed__3_once, _init_l_Lean_Parser_Level_imax_formatter___closed__3);
v___x_594_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_592_, v___x_593_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_formatter___boxed(lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Parser_Level_imax_formatter(v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7(){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_608_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_609_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_610_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0));
v___x_611_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_imax_formatter___boxed), 5, 0);
v___x_612_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_608_, v___x_609_, v___x_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___boxed(lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
return v_res_614_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Lean_Parser_Level_max_parenthesizer___closed__5, &l_Lean_Parser_Level_max_parenthesizer___closed__5_once, _init_l_Lean_Parser_Level_max_parenthesizer___closed__5);
v___x_627_ = ((lean_object*)(l_Lean_Parser_Level_imax_parenthesizer___closed__1));
v___x_628_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_628_, 0, v___x_627_);
lean_closure_set(v___x_628_, 1, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Parser_Level_imax_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_obj_once(&l_Lean_Parser_Level_imax_parenthesizer___closed__2, &l_Lean_Parser_Level_imax_parenthesizer___closed__2_once, _init_l_Lean_Parser_Level_imax_parenthesizer___closed__2);
v___x_630_ = lean_unsigned_to_nat(1024u);
v___x_631_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_632_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_632_, 0, v___x_631_);
lean_closure_set(v___x_632_, 1, v___x_630_);
lean_closure_set(v___x_632_, 2, v___x_629_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_parenthesizer(lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((lean_object*)(l_Lean_Parser_Level_imax_parenthesizer___closed__0));
v___x_639_ = lean_obj_once(&l_Lean_Parser_Level_imax_parenthesizer___closed__3, &l_Lean_Parser_Level_imax_parenthesizer___closed__3_once, _init_l_Lean_Parser_Level_imax_parenthesizer___closed__3);
v___x_640_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_638_, v___x_639_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_imax_parenthesizer___boxed(lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Parser_Level_imax_parenthesizer(v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11(){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_654_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_655_ = ((lean_object*)(l_Lean_Parser_Level_imax___closed__1));
v___x_656_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0));
v___x_657_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_imax_parenthesizer___boxed), 5, 0);
v___x_658_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_654_, v___x_655_, v___x_656_, v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___boxed(lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
return v_res_660_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__2(void){
_start:
{
uint8_t v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = 0;
v___x_668_ = 1;
v___x_669_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_670_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__0));
v___x_671_ = l_Lean_Parser_mkAntiquot(v___x_670_, v___x_669_, v___x_668_, v___x_667_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__4(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__3));
v___x_674_ = l_Lean_Parser_symbol(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__5(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__4, &l_Lean_Parser_Level_hole___closed__4_once, _init_l_Lean_Parser_Level_hole___closed__4);
v___x_676_ = lean_unsigned_to_nat(1024u);
v___x_677_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_678_ = l_Lean_Parser_leadingNode(v___x_677_, v___x_676_, v___x_675_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__6(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__5, &l_Lean_Parser_Level_hole___closed__5_once, _init_l_Lean_Parser_Level_hole___closed__5);
v___x_680_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__2, &l_Lean_Parser_Level_hole___closed__2_once, _init_l_Lean_Parser_Level_hole___closed__2);
v___x_681_ = l_Lean_Parser_withAntiquot(v___x_680_, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole___closed__7(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__6, &l_Lean_Parser_Level_hole___closed__6_once, _init_l_Lean_Parser_Level_hole___closed__6);
v___x_683_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_684_ = l_Lean_Parser_withCache(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Parser_Level_hole(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Lean_Parser_Level_hole___closed__7, &l_Lean_Parser_Level_hole___closed__7_once, _init_l_Lean_Parser_Level_hole___closed__7);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1(){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_687_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_688_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_689_ = l_Lean_Parser_Level_hole;
v___x_690_ = lean_unsigned_to_nat(1000u);
v___x_691_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_687_, v___x_688_, v___x_689_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1___boxed(lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3(){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_721_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6));
v___x_722_ = l_Lean_addBuiltinDeclarationRanges(v___x_720_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___boxed(lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_formatter(lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l_Lean_Parser_Level_hole_formatter___closed__0));
v___x_744_ = ((lean_object*)(l_Lean_Parser_Level_hole_formatter___closed__2));
v___x_745_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_743_, v___x_744_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_formatter___boxed(lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Parser_Level_hole_formatter(v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7(){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_759_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_760_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_761_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0));
v___x_762_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_hole_formatter___boxed), 5, 0);
v___x_763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_759_, v___x_760_, v___x_761_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___boxed(lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_parenthesizer(lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((lean_object*)(l_Lean_Parser_Level_hole_parenthesizer___closed__0));
v___x_785_ = ((lean_object*)(l_Lean_Parser_Level_hole_parenthesizer___closed__2));
v___x_786_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_784_, v___x_785_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_hole_parenthesizer___boxed(lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Parser_Level_hole_parenthesizer(v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11(){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_800_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_801_ = ((lean_object*)(l_Lean_Parser_Level_hole___closed__1));
v___x_802_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0));
v___x_803_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_hole_parenthesizer___boxed), 5, 0);
v___x_804_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_800_, v___x_801_, v___x_802_, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___boxed(lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
return v_res_806_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num___closed__0(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = l_Lean_Parser_maxPrec;
v___x_808_ = l_Lean_Parser_checkPrec(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = l_Lean_Parser_numLit;
v___x_810_ = lean_obj_once(&l_Lean_Parser_Level_num___closed__0, &l_Lean_Parser_Level_num___closed__0_once, _init_l_Lean_Parser_Level_num___closed__0);
v___x_811_ = l_Lean_Parser_andthen(v___x_810_, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_Lean_Parser_Level_num___closed__1, &l_Lean_Parser_Level_num___closed__1_once, _init_l_Lean_Parser_Level_num___closed__1);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1(){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_820_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_821_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1));
v___x_822_ = l_Lean_Parser_Level_num;
v___x_823_ = lean_unsigned_to_nat(1000u);
v___x_824_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_820_, v___x_821_, v___x_822_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___boxed(lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3(){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1));
v___x_852_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6));
v___x_853_ = l_Lean_addBuiltinDeclarationRanges(v___x_851_, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___boxed(lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_formatter(lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
v___x_863_ = ((lean_object*)(l_Lean_Parser_Level_num_formatter___closed__0));
v___x_864_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_862_, v___x_863_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_formatter___boxed(lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Parser_Level_num_formatter(v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___lam__0(lean_object* v___x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(v___x_871_, v___y_873_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed(lean_object* v___x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Parser_Level_num_parenthesizer___lam__0(v___x_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Parser_Level_num_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_885_; lean_object* v___f_886_; 
v___x_885_ = l_Lean_Parser_maxPrec;
v___f_886_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_886_, 0, v___x_885_);
return v___f_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer(lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___f_893_ = lean_obj_once(&l_Lean_Parser_Level_num_parenthesizer___closed__0, &l_Lean_Parser_Level_num_parenthesizer___closed__0_once, _init_l_Lean_Parser_Level_num_parenthesizer___closed__0);
v___x_894_ = ((lean_object*)(l_Lean_Parser_Level_num_parenthesizer___closed__1));
v___x_895_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___f_893_, v___x_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_num_parenthesizer___boxed(lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Parser_Level_num_parenthesizer(v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Parser_Level_ident___closed__0(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = l_Lean_Parser_ident;
v___x_903_ = lean_obj_once(&l_Lean_Parser_Level_num___closed__0, &l_Lean_Parser_Level_num___closed__0_once, _init_l_Lean_Parser_Level_num___closed__0);
v___x_904_ = l_Lean_Parser_andthen(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Parser_Level_ident(void){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l_Lean_Parser_Level_ident___closed__0, &l_Lean_Parser_Level_ident___closed__0_once, _init_l_Lean_Parser_Level_ident___closed__0);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1(){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_913_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_914_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1));
v___x_915_ = l_Lean_Parser_Level_ident;
v___x_916_ = lean_unsigned_to_nat(1000u);
v___x_917_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_913_, v___x_914_, v___x_915_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___boxed(lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3(){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1));
v___x_947_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6));
v___x_948_ = l_Lean_addBuiltinDeclarationRanges(v___x_946_, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___boxed(lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_formatter(lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
v___x_958_ = ((lean_object*)(l_Lean_Parser_Level_ident_formatter___closed__0));
v___x_959_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_957_, v___x_958_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_formatter___boxed(lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Parser_Level_ident_formatter(v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_parenthesizer(lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___f_972_ = lean_obj_once(&l_Lean_Parser_Level_num_parenthesizer___closed__0, &l_Lean_Parser_Level_num_parenthesizer___closed__0_once, _init_l_Lean_Parser_Level_num_parenthesizer___closed__0);
v___x_973_ = ((lean_object*)(l_Lean_Parser_Level_ident_parenthesizer___closed__0));
v___x_974_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___f_972_, v___x_973_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_ident_parenthesizer___boxed(lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Parser_Level_ident_parenthesizer(v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit___closed__3(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__2));
v___x_989_ = l_Lean_Parser_symbol(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit___closed__4(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = l_Lean_Parser_numLit;
v___x_991_ = lean_obj_once(&l_Lean_Parser_Level_addLit___closed__3, &l_Lean_Parser_Level_addLit___closed__3_once, _init_l_Lean_Parser_Level_addLit___closed__3);
v___x_992_ = l_Lean_Parser_andthen(v___x_991_, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit___closed__5(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_993_ = lean_obj_once(&l_Lean_Parser_Level_addLit___closed__4, &l_Lean_Parser_Level_addLit___closed__4_once, _init_l_Lean_Parser_Level_addLit___closed__4);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_unsigned_to_nat(65u);
v___x_996_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_997_ = l_Lean_Parser_trailingNode(v___x_996_, v___x_995_, v___x_994_, v___x_993_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Parser_Level_addLit(void){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_obj_once(&l_Lean_Parser_Level_addLit___closed__5, &l_Lean_Parser_Level_addLit___closed__5_once, _init_l_Lean_Parser_Level_addLit___closed__5);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1(){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1000_ = ((lean_object*)(l_Lean_Parser_levelParser___closed__0));
v___x_1001_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1002_ = l_Lean_Parser_Level_addLit;
v___x_1003_ = lean_unsigned_to_nat(1000u);
v___x_1004_ = l_Lean_Parser_addBuiltinTrailingParser(v___x_1000_, v___x_1001_, v___x_1002_, v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1___boxed(lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3(){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1034_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6));
v___x_1035_ = l_Lean_addBuiltinDeclarationRanges(v___x_1033_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___boxed(lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_formatter(lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1049_ = ((lean_object*)(l_Lean_Parser_Level_addLit_formatter___closed__1));
v___x_1050_ = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(v___x_1048_, v___x_1049_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_formatter___boxed(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Parser_Level_addLit_formatter(v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7(){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1064_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1065_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1066_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0));
v___x_1067_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_addLit_formatter___boxed), 5, 0);
v___x_1068_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1064_, v___x_1065_, v___x_1066_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___boxed(lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_parenthesizer(lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1081_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1082_ = lean_unsigned_to_nat(65u);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = ((lean_object*)(l_Lean_Parser_Level_addLit_parenthesizer___closed__1));
v___x_1085_ = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(v___x_1081_, v___x_1082_, v___x_1083_, v___x_1084_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Level_addLit_parenthesizer___boxed(lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Parser_Level_addLit_parenthesizer(v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11(){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1099_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1100_ = ((lean_object*)(l_Lean_Parser_Level_addLit___closed__1));
v___x_1101_ = ((lean_object*)(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0));
v___x_1102_ = lean_alloc_closure((void*)(l_Lean_Parser_Level_addLit_parenthesizer___boxed), 5, 0);
v___x_1103_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1099_, v___x_1100_, v___x_1101_, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___boxed(lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
return v_res_1105_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
