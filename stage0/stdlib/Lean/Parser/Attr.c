// Lean compiler output
// Module: Lean.Parser.Attr
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkPrec(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_prio_parser"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 62, 206, 117, 66, 228, 175, 129)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Category"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 107, 2, 165, 49, 177, 197, 179)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 65, 23, 56, 30, 174, 149, 234)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(230, 189, 113, 236, 149, 162, 75, 196)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 57, 71, 43, 179, 220, 236, 177)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 92, 158, 115, 76, 147, 54, 64)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 246, 167, 225, 21, 233, 106, 254)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 97, 220, 102, 149, 211, 249, 136)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 7, 108, 95, 197, 217, 133, 199)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 97, 179, 25, 134, 12, 176, 74)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 94, 63, 146, 254, 93, 55, 154)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1857506627) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(36, 161, 140, 23, 58, 214, 182, 21)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 142, 31, 72, 26, 190, 190, 177)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 51, 32, 68, 30, 111, 172, 29)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(222, 234, 60, 150, 20, 158, 160, 29)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "prio_parser"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 192, 223, 117, 127, 39, 55, 31)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_attr_parser"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 71, 13, 255, 49, 148, 157, 196)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(6, 185, 156, 91, 160, 100, 34, 125)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),((lean_object*)(((size_t)(249558774) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(227, 21, 132, 234, 73, 97, 121, 52)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 226, 234, 163, 45, 129, 3, 160)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 41, 138, 128, 134, 189, 149, 202)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(69, 34, 192, 223, 89, 207, 46, 132)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "attr_parser"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 118, 202, 56, 176, 36, 29, 40)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Priority_numPrio___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Priority_numPrio___closed__0;
static lean_once_cell_t l_Lean_Parser_Priority_numPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Priority_numPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Priority"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numPrio"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 3, 140, 143, 23, 192, 98, 73)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(62, 56, 13, 47, 63, 33, 83, 156)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Priority_numPrio_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Priority_numPrio_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Priority_numPrio_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0;
static const lean_closure_object l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Attr_simple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Parser_Attr_simple___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_simple___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_simple___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_simple___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_simple___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_simple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_simple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Parser_Attr_simple___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__8;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__9;
static lean_once_cell_t l_Lean_Parser_Attr_simple___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_simple___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(113) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value),((lean_object*)(((size_t)(113) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Attr_simple_formatter___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_priorityParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__3_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_simple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 229, 191, 246, 47, 244, 239, 84)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppSpace_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_priorityParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Parser_Attr_simple_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value)} };
static const lean_object* l_Lean_Parser_Attr_simple_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_simple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 123, 213, 83, 58, 188, 82, 100)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_macro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Parser_Attr_macro___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_macro___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_macro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_macro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_macro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_macro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_macro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Parser_Attr_macro___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_macro___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_macro___closed__2;
static const lean_string_object l_Lean_Parser_Attr_macro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "macro "};
static const lean_object* l_Lean_Parser_Attr_macro___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_macro___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_macro___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_macro___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_macro___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_macro___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_macro___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_macro___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_macro___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_macro___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_macro___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_macro___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_macro_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_macro_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_macro_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_macro_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_macro_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_macro_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_macro_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_macro_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_macro_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_macro_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_macro_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_macro_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_macro_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_macro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 38, 245, 236, 190, 18, 200, 255)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_macro_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_macro_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_macro_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_macro_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_macro_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_macro_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_macro___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_macro_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_macro_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_macro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 178, 73, 41, 185, 64, 194, 161)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_export___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Parser_Attr_export___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_export___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_export___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_export___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_export___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_export___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_export___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_object* l_Lean_Parser_Attr_export___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_export___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_export___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_export___closed__2;
static const lean_string_object l_Lean_Parser_Attr_export___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "export "};
static const lean_object* l_Lean_Parser_Attr_export___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_export___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_export___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_export___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_export___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_export___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_export___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_export___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_export___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_export___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_export___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_export___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(74) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value),((lean_object*)(((size_t)(74) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_export_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_export_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_export_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_export_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_export_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_export_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_export_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_export_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_export_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_export_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_export_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_export_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_export_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_export___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 151, 18, 12, 107, 65, 124, 243)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_export_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_export_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_export_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_export_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_export_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_export_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_export_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_export_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_export_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_export_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_export___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_export_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_export_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_export_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_export___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 202, 214, 57, 107, 104, 12, 237)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_recursor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "recursor"};
static const lean_object* l_Lean_Parser_Attr_recursor___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_recursor___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_recursor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_recursor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_recursor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_recursor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_recursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 29, 106, 40, 200, 118, 31, 85)}};
static const lean_object* l_Lean_Parser_Attr_recursor___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_recursor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_recursor___closed__2;
static const lean_string_object l_Lean_Parser_Attr_recursor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "recursor "};
static const lean_object* l_Lean_Parser_Attr_recursor___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_recursor___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Attr_recursor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_recursor___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_recursor___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_recursor___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_recursor___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_recursor___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_recursor___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_recursor___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_recursor___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_recursor___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(101) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value),((lean_object*)(((size_t)(101) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_recursor_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_recursor_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_recursor_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_recursor_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_recursor_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_recursor_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_recursor_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_recursor_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_recursor_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_recursor_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_recursor_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_recursor_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_recursor_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_recursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 29, 106, 40, 200, 118, 31, 85)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 2, 9, 92, 3, 102, 239, 12)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_recursor_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_recursor_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_recursor_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_recursor_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_recursor_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_recursor_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_recursor___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_recursor_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_recursor_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_recursor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 29, 106, 40, 200, 118, 31, 85)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 47, 55, 250, 244, 14, 194, 236)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_class___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l_Lean_Parser_Attr_class___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_class___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_class___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_class___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_class___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_class___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_object* l_Lean_Parser_Attr_class___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_class___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_class___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_class___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_class___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_class___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_class___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_class___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_class___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_class___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_class___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_class___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_class_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_class_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_class_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_class_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_class_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_class_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_class_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_class_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_class_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_class_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 161, 70, 79, 21, 219, 219, 187)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_class_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_class_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_class_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_class_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_class_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_class_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_class_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_class___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_class_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_class_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_class_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_class___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 183, 192, 212, 26, 200, 245, 145)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_instance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lean_Parser_Attr_instance___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_instance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_instance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_instance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_instance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_object* l_Lean_Parser_Attr_instance___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__8;
static lean_once_cell_t l_Lean_Parser_Attr_instance___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_instance___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)(((size_t)(112) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value),((lean_object*)(((size_t)(112) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_instance_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_instance_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 225, 246, 137, 65, 110, 208, 211)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_instance_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_instance_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_instance_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_instance___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_instance_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_instance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 44, 88, 85, 16, 38, 144, 111)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_default__instance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "default_instance"};
static const lean_object* l_Lean_Parser_Attr_default__instance___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_default__instance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_default__instance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_default__instance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_default__instance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 215, 188, 14, 80, 67, 224, 116)}};
static const lean_object* l_Lean_Parser_Attr_default__instance___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_default__instance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_default__instance___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_default__instance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_default__instance___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_default__instance___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_default__instance___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_default__instance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_default__instance___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_default__instance___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_default__instance___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_default__instance___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_default__instance___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(138) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value),((lean_object*)(((size_t)(138) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_default__instance_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_default__instance_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_default__instance_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_default__instance_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_default__instance_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_instance_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_default__instance_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_default__instance_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_default__instance_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_default__instance_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 215, 188, 14, 80, 67, 224, 116)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 112, 171, 71, 131, 75, 3, 107)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_default__instance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 215, 188, 14, 80, 67, 224, 116)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 170, 216, 200, 27, 58, 15, 9)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_specialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l_Lean_Parser_Attr_specialize___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_specialize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_specialize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_specialize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_specialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 28, 50, 2, 100, 118, 84, 52)}};
static const lean_object* l_Lean_Parser_Attr_specialize___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__8;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__9;
static lean_once_cell_t l_Lean_Parser_Attr_specialize___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_specialize___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)(((size_t)(134) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value),((lean_object*)(((size_t)(134) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_specialize_formatter___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 28, 50, 2, 100, 118, 84, 52)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 88, 144, 13, 224, 198, 112, 184)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Attr_specialize_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_specialize___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_specialize_parenthesizer___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_specialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 28, 50, 2, 100, 118, 84, 52)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 146, 129, 38, 159, 182, 72, 140)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_externEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "externEntry"};
static const lean_object* l_Lean_Parser_Attr_externEntry___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_externEntry___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_externEntry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_externEntry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_externEntry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_externEntry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 120, 255, 6, 244, 195, 179, 180)}};
static const lean_object* l_Lean_Parser_Attr_externEntry___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__4;
static const lean_string_object l_Lean_Parser_Attr_externEntry___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "inline "};
static const lean_object* l_Lean_Parser_Attr_externEntry___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_externEntry___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__8;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__9;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__10;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__11;
static lean_once_cell_t l_Lean_Parser_Attr_externEntry___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_externEntry___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry;
static const lean_string_object l_Lean_Parser_Attr_extern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l_Lean_Parser_Attr_extern___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_extern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_extern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_extern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_extern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 126, 252, 124, 35, 62, 180, 112)}};
static const lean_object* l_Lean_Parser_Attr_extern___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_extern___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__8;
static lean_once_cell_t l_Lean_Parser_Attr_extern___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(93) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value),((lean_object*)(((size_t)(93) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 120, 255, 6, 244, 195, 179, 180)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 209, 196, 10, 229, 104, 88, 235)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_extern_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_extern___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_extern_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_extern_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_extern_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_extern_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_extern_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_extern_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_extern_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_extern_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_extern_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 126, 252, 124, 35, 62, 180, 112)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 8, 91, 19, 215, 171, 128, 249)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_strLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value),((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value)} };
static const lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_externEntry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 120, 255, 6, 244, 195, 179, 180)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 76, 95, 57, 63, 140, 230, 190)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_extern_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_extern___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_extern_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_extern_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_extern_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_extern_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_extern_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_extern_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_extern_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_extern_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_extern_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_extern_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_extern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 126, 252, 124, 35, 62, 180, 112)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 28, 254, 72, 236, 212, 80, 70)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_tactic__alt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_alt"};
static const lean_object* l_Lean_Parser_Attr_tactic__alt___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__alt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 168, 96, 206, 229, 58, 101)}};
static const lean_object* l_Lean_Parser_Attr_tactic__alt___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__alt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__alt___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 208, .m_capacity = 208, .m_length = 207, .m_data = "Declares this tactic to be an alias or alternative form of an existing tactic.\n\nThis has the following effects:\n* The alias relationship is saved\n* The docstring is taken from the original tactic, if present"};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(61) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 168, 96, 206, 229, 58, 101)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 174, 15, 101, 134, 196, 196, 73)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__alt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 168, 96, 206, 229, 58, 101)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 105, 16, 60, 122, 191, 76, 132)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_tactic__tag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_tag"};
static const lean_object* l_Lean_Parser_Attr_tactic__tag___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__tag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 70, 119, 85, 147, 120, 119, 38)}};
static const lean_object* l_Lean_Parser_Attr_tactic__tag___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__tag___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__tag___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "Adds one or more tags to a tactic.\n\nTags should be applied to the canonical names for tactics."};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(69) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value),((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_formatter___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 70, 119, 85, 147, 120, 119, 38)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 156, 211, 23, 66, 168, 121, 85)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many1_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__tag___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 70, 119, 85, 147, 120, 119, 38)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 101, 40, 71, 142, 150, 231, 238)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_tactic__name___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_name"};
static const lean_object* l_Lean_Parser_Attr_tactic__name___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_tactic__name___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 253, 162, 55, 13, 176, 86, 10)}};
static const lean_object* l_Lean_Parser_Attr_tactic__name___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__2;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__3;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__4;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__5;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__6;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__7;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__8;
static lean_once_cell_t l_Lean_Parser_Attr_tactic__name___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Attr_tactic__name___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 391, .m_capacity = 391, .m_length = 390, .m_data = "Sets the tactic's name.\n\nOrdinarily, tactic names are automatically set to the first token in the tactic's parser. If this\nprocess fails, or if the tactic's name should be multiple tokens (e.g. `let rec`), then this\nattribute can be used to provide a name.\n\nThe tactic's name is used in documentation as well as in completion. Thus, the name should be a\nvalid prefix of the tactic's syntax."};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_formatter___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 253, 162, 55, 13, 176, 86, 10)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 115, 32, 33, 176, 74, 73, 63)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value),((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_tactic__name___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 253, 162, 55, 13, 176, 86, 10)}};
static const lean_ctor_object l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 5, 121, 30, 21, 6, 250, 91)}};
static const lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___boxed(lean_object*);
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_74_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_75_ = 2;
v___x_76_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_77_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_73_, v___x_74_, v___x_75_, v___x_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec_ref_known(v___x_77_, 1);
v___x_78_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_79_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_80_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_78_, v___x_79_, v___x_76_);
return v___x_80_;
}
else
{
return v___x_77_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
return v_res_83_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_112_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_113_ = 1;
v___x_114_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_115_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_111_, v___x_112_, v___x_113_, v___x_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_117_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_118_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_116_, v___x_117_, v___x_114_);
return v___x_118_;
}
else
{
return v___x_115_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_119_;
v_res_119_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2____boxed(lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser(lean_object* v_rbp_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_124_ = l_Lean_Parser_categoryParser(v___x_123_, v_rbp_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser(lean_object* v_rbp_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_127_ = l_Lean_Parser_categoryParser(v___x_126_, v_rbp_125_);
return v___x_127_;
}
}
lean_object* l_Lean_Parser_priorityParser_formatter___redArg(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_134_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_133_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_134_;
}
}
LEAN_EXPORT void l_Lean_Parser_priorityParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_128_ = stack[0].m_obj;
lean_object* v_a_129_ = stack[1].m_obj;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_a_131_ = stack[3].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_Lean_Parser_priorityParser_formatter___redArg(v_a_128_, v_a_129_, v_a_130_, v_a_131_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___redArg___boxed(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Parser_priorityParser_formatter___redArg(v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_141_;
}
}
lean_object* l_Lean_Parser_priorityParser_formatter(lean_object* v_rbp_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Parser_priorityParser_formatter___redArg(v_a_143_, v_a_144_, v_a_145_, v_a_146_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Parser_priorityParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_142_ = stack[0].m_obj;
lean_object* v_a_143_ = stack[1].m_obj;
lean_object* v_a_144_ = stack[2].m_obj;
lean_object* v_a_145_ = stack[3].m_obj;
lean_object* v_a_146_ = stack[4].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Parser_priorityParser_formatter(v_rbp_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___boxed(lean_object* v_rbp_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Parser_priorityParser_formatter(v_rbp_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_rbp_150_);
return v_res_156_;
}
}
lean_object* l_Lean_Parser_priorityParser_parenthesizer(lean_object* v_rbp_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_164_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_163_, v_rbp_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Lean_Parser_priorityParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_157_ = stack[0].m_obj;
lean_object* v_a_158_ = stack[1].m_obj;
lean_object* v_a_159_ = stack[2].m_obj;
lean_object* v_a_160_ = stack[3].m_obj;
lean_object* v_a_161_ = stack[4].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Lean_Parser_priorityParser_parenthesizer(v_rbp_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_parenthesizer___boxed(lean_object* v_rbp_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Parser_priorityParser_parenthesizer(v_rbp_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
return v_res_172_;
}
}
lean_object* l_Lean_Parser_attrParser_formatter___redArg(lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_179_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(v___x_178_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Parser_attrParser_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_173_ = stack[0].m_obj;
lean_object* v_a_174_ = stack[1].m_obj;
lean_object* v_a_175_ = stack[2].m_obj;
lean_object* v_a_176_ = stack[3].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_Parser_attrParser_formatter___redArg(v_a_173_, v_a_174_, v_a_175_, v_a_176_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___redArg___boxed(lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Parser_attrParser_formatter___redArg(v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_186_;
}
}
lean_object* l_Lean_Parser_attrParser_formatter(lean_object* v_rbp_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Parser_attrParser_formatter___redArg(v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_Parser_attrParser_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_187_ = stack[0].m_obj;
lean_object* v_a_188_ = stack[1].m_obj;
lean_object* v_a_189_ = stack[2].m_obj;
lean_object* v_a_190_ = stack[3].m_obj;
lean_object* v_a_191_ = stack[4].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_Parser_attrParser_formatter(v_rbp_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___boxed(lean_object* v_rbp_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Parser_attrParser_formatter(v_rbp_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_rbp_195_);
return v_res_201_;
}
}
lean_object* l_Lean_Parser_attrParser_parenthesizer(lean_object* v_rbp_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_209_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(v___x_208_, v_rbp_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_Parser_attrParser_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_rbp_202_ = stack[0].m_obj;
lean_object* v_a_203_ = stack[1].m_obj;
lean_object* v_a_204_ = stack[2].m_obj;
lean_object* v_a_205_ = stack[3].m_obj;
lean_object* v_a_206_ = stack[4].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Parser_attrParser_parenthesizer(v_rbp_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_parenthesizer___boxed(lean_object* v_rbp_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Parser_attrParser_parenthesizer(v_rbp_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Parser_Priority_numPrio___closed__0(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = l_Lean_Parser_maxPrec;
v___x_219_ = l_Lean_Parser_checkPrec(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Parser_Priority_numPrio___closed__1(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = l_Lean_Parser_numLit;
v___x_221_ = lean_obj_once(&l_Lean_Parser_Priority_numPrio___closed__0, &l_Lean_Parser_Priority_numPrio___closed__0_once, _init_l_Lean_Parser_Priority_numPrio___closed__0);
v___x_222_ = l_Lean_Parser_andthen(v___x_221_, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Parser_Priority_numPrio(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_Parser_Priority_numPrio___closed__1, &l_Lean_Parser_Priority_numPrio___closed__1_once, _init_l_Lean_Parser_Priority_numPrio___closed__1);
return v___x_223_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1(){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_233_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2));
v___x_234_ = l_Lean_Parser_Priority_numPrio;
v___x_235_ = lean_unsigned_to_nat(1000u);
v___x_236_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_232_, v___x_233_, v___x_234_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_237_;
v_res_237_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___boxed(lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
return v_res_239_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3(){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2));
v___x_267_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6));
v___x_268_ = l_Lean_addBuiltinDeclarationRanges(v___x_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_269_;
v_res_269_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___boxed(lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
return v_res_271_;
}
}
lean_object* l_Lean_Parser_Priority_numPrio_formatter(lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
v___x_279_ = ((lean_object*)(l_Lean_Parser_Priority_numPrio_formatter___closed__0));
v___x_280_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(v___x_278_, v___x_279_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_280_;
}
}
LEAN_EXPORT void l_Lean_Parser_Priority_numPrio_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_273_ = stack[0].m_obj;
lean_object* v_a_274_ = stack[1].m_obj;
lean_object* v_a_275_ = stack[2].m_obj;
lean_object* v_a_276_ = stack[3].m_obj;
lean_object* v_res_281_;
v_res_281_ = l_Lean_Parser_Priority_numPrio_formatter(v_a_273_, v_a_274_, v_a_275_, v_a_276_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_formatter___boxed(lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Parser_Priority_numPrio_formatter(v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_287_;
}
}
lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(lean_object* v___x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(v___x_288_, v___y_290_);
return v___x_294_;
}
}
LEAN_EXPORT void l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_288_ = stack[0].m_obj;
lean_object* v___y_289_ = stack[1].m_obj;
lean_object* v___y_290_ = stack[2].m_obj;
lean_object* v___y_291_ = stack[3].m_obj;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(v___x_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed(lean_object* v___x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(v___x_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
static lean_object* _init_l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_303_; lean_object* v___f_304_; 
v___x_303_ = l_Lean_Parser_maxPrec;
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(v___f_304_, 0, v___x_303_);
return v___f_304_;
}
}
lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer(lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___f_311_ = lean_obj_once(&l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0, &l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0_once, _init_l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0);
v___x_312_ = ((lean_object*)(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1));
v___x_313_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___f_311_, v___x_312_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_313_;
}
}
LEAN_EXPORT void l_Lean_Parser_Priority_numPrio_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_306_ = stack[0].m_obj;
lean_object* v_a_307_ = stack[1].m_obj;
lean_object* v_a_308_ = stack[2].m_obj;
lean_object* v_a_309_ = stack[3].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lean_Parser_Priority_numPrio_parenthesizer(v_a_306_, v_a_307_, v_a_308_, v_a_309_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___boxed(lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Parser_Priority_numPrio_parenthesizer(v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_320_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__2(void){
_start:
{
uint8_t v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = 0;
v___x_328_ = 1;
v___x_329_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_330_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__0));
v___x_331_ = l_Lean_Parser_mkAntiquot(v___x_330_, v___x_329_, v___x_328_, v___x_327_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__3(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_));
v___x_334_ = l_Lean_Parser_categoryParser(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__4(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Lean_Parser_ident;
v___x_336_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__3, &l_Lean_Parser_Attr_simple___closed__3_once, _init_l_Lean_Parser_Attr_simple___closed__3);
v___x_337_ = l_Lean_Parser_orelse(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__5(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__4, &l_Lean_Parser_Attr_simple___closed__4_once, _init_l_Lean_Parser_Attr_simple___closed__4);
v___x_339_ = l_Lean_Parser_skip;
v___x_340_ = l_Lean_Parser_andthen(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__6(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__5, &l_Lean_Parser_Attr_simple___closed__5_once, _init_l_Lean_Parser_Attr_simple___closed__5);
v___x_342_ = l_Lean_Parser_optional(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__7(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__6, &l_Lean_Parser_Attr_simple___closed__6_once, _init_l_Lean_Parser_Attr_simple___closed__6);
v___x_344_ = l_Lean_Parser_ident;
v___x_345_ = l_Lean_Parser_andthen(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__8(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__7, &l_Lean_Parser_Attr_simple___closed__7_once, _init_l_Lean_Parser_Attr_simple___closed__7);
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_349_ = l_Lean_Parser_leadingNode(v___x_348_, v___x_347_, v___x_346_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__9(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__8, &l_Lean_Parser_Attr_simple___closed__8_once, _init_l_Lean_Parser_Attr_simple___closed__8);
v___x_351_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__2, &l_Lean_Parser_Attr_simple___closed__2_once, _init_l_Lean_Parser_Attr_simple___closed__2);
v___x_352_ = l_Lean_Parser_withAntiquot(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple___closed__10(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__9, &l_Lean_Parser_Attr_simple___closed__9_once, _init_l_Lean_Parser_Attr_simple___closed__9);
v___x_354_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_355_ = l_Lean_Parser_withCache(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__10, &l_Lean_Parser_Attr_simple___closed__10_once, _init_l_Lean_Parser_Attr_simple___closed__10);
return v___x_356_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1(){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_359_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_360_ = l_Lean_Parser_Attr_simple;
v___x_361_ = lean_unsigned_to_nat(1000u);
v___x_362_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_358_, v___x_359_, v___x_360_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_363_;
v_res_363_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1___boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
return v_res_365_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3(){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_393_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6));
v___x_394_ = l_Lean_addBuiltinDeclarationRanges(v___x_392_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_395_;
v_res_395_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___boxed(lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
return v_res_397_;
}
}
lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0(lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_399_);
return v___x_403_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_simple_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_398_ = stack[0].m_obj;
lean_object* v___y_399_ = stack[1].m_obj;
lean_object* v___y_400_ = stack[2].m_obj;
lean_object* v___y_401_ = stack[3].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lean_Parser_Attr_simple_formatter___lam__0(v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0___boxed(lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Parser_Attr_simple_formatter___lam__0(v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
lean_object* l_Lean_Parser_Attr_simple_formatter(lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_Parser_Attr_simple_formatter___closed__1));
v___x_443_ = ((lean_object*)(l_Lean_Parser_Attr_simple_formatter___closed__8));
v___x_444_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_442_, v___x_443_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_simple_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_437_ = stack[0].m_obj;
lean_object* v_a_438_ = stack[1].m_obj;
lean_object* v_a_439_ = stack[2].m_obj;
lean_object* v_a_440_ = stack[3].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Parser_Attr_simple_formatter(v_a_437_, v_a_438_, v_a_439_, v_a_440_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___boxed(lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Parser_Attr_simple_formatter(v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
return v_res_451_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_460_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_461_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_462_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1));
v___x_463_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___boxed), 5, 0);
v___x_464_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_460_, v___x_461_, v___x_462_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_465_;
v_res_465_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___boxed(lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
return v_res_467_;
}
}
lean_object* l_Lean_Parser_Attr_simple_parenthesizer(lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((lean_object*)(l_Lean_Parser_Attr_simple_parenthesizer___closed__0));
v___x_500_ = ((lean_object*)(l_Lean_Parser_Attr_simple_parenthesizer___closed__8));
v___x_501_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_499_, v___x_500_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_501_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_simple_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_494_ = stack[0].m_obj;
lean_object* v_a_495_ = stack[1].m_obj;
lean_object* v_a_496_ = stack[2].m_obj;
lean_object* v_a_497_ = stack[3].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Parser_Attr_simple_parenthesizer(v_a_494_, v_a_495_, v_a_496_, v_a_497_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer___boxed(lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Parser_Attr_simple_parenthesizer(v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_508_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11(){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_517_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_518_ = ((lean_object*)(l_Lean_Parser_Attr_simple___closed__1));
v___x_519_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1));
v___x_520_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___boxed), 5, 0);
v___x_521_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_517_, v___x_518_, v___x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_522_;
v_res_522_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___boxed(lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
return v_res_524_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro___closed__2(void){
_start:
{
uint8_t v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_531_ = 0;
v___x_532_ = 1;
v___x_533_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_534_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__0));
v___x_535_ = l_Lean_Parser_mkAntiquot(v___x_534_, v___x_533_, v___x_532_, v___x_531_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro___closed__4(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__3));
v___x_538_ = l_Lean_Parser_symbol(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_Parser_ident;
v___x_540_ = lean_obj_once(&l_Lean_Parser_Attr_macro___closed__4, &l_Lean_Parser_Attr_macro___closed__4_once, _init_l_Lean_Parser_Attr_macro___closed__4);
v___x_541_ = l_Lean_Parser_andthen(v___x_540_, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro___closed__6(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = lean_obj_once(&l_Lean_Parser_Attr_macro___closed__5, &l_Lean_Parser_Attr_macro___closed__5_once, _init_l_Lean_Parser_Attr_macro___closed__5);
v___x_543_ = lean_unsigned_to_nat(1024u);
v___x_544_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_545_ = l_Lean_Parser_leadingNode(v___x_544_, v___x_543_, v___x_542_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro___closed__7(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_obj_once(&l_Lean_Parser_Attr_macro___closed__6, &l_Lean_Parser_Attr_macro___closed__6_once, _init_l_Lean_Parser_Attr_macro___closed__6);
v___x_547_ = lean_obj_once(&l_Lean_Parser_Attr_macro___closed__2, &l_Lean_Parser_Attr_macro___closed__2_once, _init_l_Lean_Parser_Attr_macro___closed__2);
v___x_548_ = l_Lean_Parser_withAntiquot(v___x_547_, v___x_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro___closed__8(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_obj_once(&l_Lean_Parser_Attr_macro___closed__7, &l_Lean_Parser_Attr_macro___closed__7_once, _init_l_Lean_Parser_Attr_macro___closed__7);
v___x_550_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_551_ = l_Lean_Parser_withCache(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro(void){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Parser_Attr_macro___closed__8, &l_Lean_Parser_Attr_macro___closed__8_once, _init_l_Lean_Parser_Attr_macro___closed__8);
return v___x_552_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1(){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_555_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_556_ = l_Lean_Parser_Attr_macro;
v___x_557_ = lean_unsigned_to_nat(1000u);
v___x_558_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_554_, v___x_555_, v___x_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_559_;
v_res_559_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1___boxed(lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
return v_res_561_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3(){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_589_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6));
v___x_590_ = l_Lean_addBuiltinDeclarationRanges(v___x_588_, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_591_;
v_res_591_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___boxed(lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
return v_res_593_;
}
}
lean_object* l_Lean_Parser_Attr_macro_formatter(lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l_Lean_Parser_Attr_macro_formatter___closed__0));
v___x_616_ = ((lean_object*)(l_Lean_Parser_Attr_macro_formatter___closed__3));
v___x_617_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_615_, v___x_616_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_macro_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_610_ = stack[0].m_obj;
lean_object* v_a_611_ = stack[1].m_obj;
lean_object* v_a_612_ = stack[2].m_obj;
lean_object* v_a_613_ = stack[3].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_Parser_Attr_macro_formatter(v_a_610_, v_a_611_, v_a_612_, v_a_613_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_formatter___boxed(lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Parser_Attr_macro_formatter(v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_624_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7(){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_633_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_634_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0));
v___x_635_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_macro_formatter___boxed), 5, 0);
v___x_636_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_632_, v___x_633_, v___x_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_637_;
v_res_637_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___boxed(lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
return v_res_639_;
}
}
lean_object* l_Lean_Parser_Attr_macro_parenthesizer(lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = ((lean_object*)(l_Lean_Parser_Attr_macro_parenthesizer___closed__0));
v___x_662_ = ((lean_object*)(l_Lean_Parser_Attr_macro_parenthesizer___closed__3));
v___x_663_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_661_, v___x_662_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_663_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_macro_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_656_ = stack[0].m_obj;
lean_object* v_a_657_ = stack[1].m_obj;
lean_object* v_a_658_ = stack[2].m_obj;
lean_object* v_a_659_ = stack[3].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Parser_Attr_macro_parenthesizer(v_a_656_, v_a_657_, v_a_658_, v_a_659_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_parenthesizer___boxed(lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Parser_Attr_macro_parenthesizer(v_a_665_, v_a_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_670_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11(){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_678_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_679_ = ((lean_object*)(l_Lean_Parser_Attr_macro___closed__1));
v___x_680_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0));
v___x_681_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_macro_parenthesizer___boxed), 5, 0);
v___x_682_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_678_, v___x_679_, v___x_680_, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_683_;
v_res_683_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___boxed(lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
return v_res_685_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export___closed__2(void){
_start:
{
uint8_t v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_692_ = 0;
v___x_693_ = 1;
v___x_694_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_695_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__0));
v___x_696_ = l_Lean_Parser_mkAntiquot(v___x_695_, v___x_694_, v___x_693_, v___x_692_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export___closed__4(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__3));
v___x_699_ = l_Lean_Parser_symbol(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export___closed__5(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_Parser_ident;
v___x_701_ = lean_obj_once(&l_Lean_Parser_Attr_export___closed__4, &l_Lean_Parser_Attr_export___closed__4_once, _init_l_Lean_Parser_Attr_export___closed__4);
v___x_702_ = l_Lean_Parser_andthen(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export___closed__6(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = lean_obj_once(&l_Lean_Parser_Attr_export___closed__5, &l_Lean_Parser_Attr_export___closed__5_once, _init_l_Lean_Parser_Attr_export___closed__5);
v___x_704_ = lean_unsigned_to_nat(1024u);
v___x_705_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_706_ = l_Lean_Parser_leadingNode(v___x_705_, v___x_704_, v___x_703_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export___closed__7(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&l_Lean_Parser_Attr_export___closed__6, &l_Lean_Parser_Attr_export___closed__6_once, _init_l_Lean_Parser_Attr_export___closed__6);
v___x_708_ = lean_obj_once(&l_Lean_Parser_Attr_export___closed__2, &l_Lean_Parser_Attr_export___closed__2_once, _init_l_Lean_Parser_Attr_export___closed__2);
v___x_709_ = l_Lean_Parser_withAntiquot(v___x_708_, v___x_707_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export___closed__8(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_obj_once(&l_Lean_Parser_Attr_export___closed__7, &l_Lean_Parser_Attr_export___closed__7_once, _init_l_Lean_Parser_Attr_export___closed__7);
v___x_711_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_712_ = l_Lean_Parser_withCache(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Parser_Attr_export___closed__8, &l_Lean_Parser_Attr_export___closed__8_once, _init_l_Lean_Parser_Attr_export___closed__8);
return v___x_713_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1(){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_716_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_717_ = l_Lean_Parser_Attr_export;
v___x_718_ = lean_unsigned_to_nat(1000u);
v___x_719_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_715_, v___x_716_, v___x_717_, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_720_;
v_res_720_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1___boxed(lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
return v_res_722_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3(){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_750_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6));
v___x_751_ = l_Lean_addBuiltinDeclarationRanges(v___x_749_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_752_;
v_res_752_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___boxed(lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
return v_res_754_;
}
}
lean_object* l_Lean_Parser_Attr_export_formatter(lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((lean_object*)(l_Lean_Parser_Attr_export_formatter___closed__0));
v___x_777_ = ((lean_object*)(l_Lean_Parser_Attr_export_formatter___closed__3));
v___x_778_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_776_, v___x_777_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
return v___x_778_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_export_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_771_ = stack[0].m_obj;
lean_object* v_a_772_ = stack[1].m_obj;
lean_object* v_a_773_ = stack[2].m_obj;
lean_object* v_a_774_ = stack[3].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Parser_Attr_export_formatter(v_a_771_, v_a_772_, v_a_773_, v_a_774_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_formatter___boxed(lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Parser_Attr_export_formatter(v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_785_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7(){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_793_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_794_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_795_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0));
v___x_796_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_export_formatter___boxed), 5, 0);
v___x_797_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_793_, v___x_794_, v___x_795_, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_798_;
v_res_798_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___boxed(lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
return v_res_800_;
}
}
lean_object* l_Lean_Parser_Attr_export_parenthesizer(lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l_Lean_Parser_Attr_export_parenthesizer___closed__0));
v___x_823_ = ((lean_object*)(l_Lean_Parser_Attr_export_parenthesizer___closed__3));
v___x_824_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_822_, v___x_823_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_824_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_export_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_817_ = stack[0].m_obj;
lean_object* v_a_818_ = stack[1].m_obj;
lean_object* v_a_819_ = stack[2].m_obj;
lean_object* v_a_820_ = stack[3].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_Parser_Attr_export_parenthesizer(v_a_817_, v_a_818_, v_a_819_, v_a_820_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_parenthesizer___boxed(lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Parser_Attr_export_parenthesizer(v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_831_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11(){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_839_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_840_ = ((lean_object*)(l_Lean_Parser_Attr_export___closed__1));
v___x_841_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0));
v___x_842_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_export_parenthesizer___boxed), 5, 0);
v___x_843_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_839_, v___x_840_, v___x_841_, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_844_;
v_res_844_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___boxed(lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
return v_res_846_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor___closed__2(void){
_start:
{
uint8_t v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = 0;
v___x_854_ = 1;
v___x_855_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_856_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__0));
v___x_857_ = l_Lean_Parser_mkAntiquot(v___x_856_, v___x_855_, v___x_854_, v___x_853_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor___closed__4(void){
_start:
{
uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 0;
v___x_860_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__3));
v___x_861_ = l_Lean_Parser_nonReservedSymbol(v___x_860_, v___x_859_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor___closed__5(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = l_Lean_Parser_numLit;
v___x_863_ = lean_obj_once(&l_Lean_Parser_Attr_recursor___closed__4, &l_Lean_Parser_Attr_recursor___closed__4_once, _init_l_Lean_Parser_Attr_recursor___closed__4);
v___x_864_ = l_Lean_Parser_andthen(v___x_863_, v___x_862_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor___closed__6(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_865_ = lean_obj_once(&l_Lean_Parser_Attr_recursor___closed__5, &l_Lean_Parser_Attr_recursor___closed__5_once, _init_l_Lean_Parser_Attr_recursor___closed__5);
v___x_866_ = lean_unsigned_to_nat(1024u);
v___x_867_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_868_ = l_Lean_Parser_leadingNode(v___x_867_, v___x_866_, v___x_865_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor___closed__7(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_obj_once(&l_Lean_Parser_Attr_recursor___closed__6, &l_Lean_Parser_Attr_recursor___closed__6_once, _init_l_Lean_Parser_Attr_recursor___closed__6);
v___x_870_ = lean_obj_once(&l_Lean_Parser_Attr_recursor___closed__2, &l_Lean_Parser_Attr_recursor___closed__2_once, _init_l_Lean_Parser_Attr_recursor___closed__2);
v___x_871_ = l_Lean_Parser_withAntiquot(v___x_870_, v___x_869_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor___closed__8(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_obj_once(&l_Lean_Parser_Attr_recursor___closed__7, &l_Lean_Parser_Attr_recursor___closed__7_once, _init_l_Lean_Parser_Attr_recursor___closed__7);
v___x_873_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_874_ = l_Lean_Parser_withCache(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor(void){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = lean_obj_once(&l_Lean_Parser_Attr_recursor___closed__8, &l_Lean_Parser_Attr_recursor___closed__8_once, _init_l_Lean_Parser_Attr_recursor___closed__8);
return v___x_875_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1(){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_878_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_879_ = l_Lean_Parser_Attr_recursor;
v___x_880_ = lean_unsigned_to_nat(1000u);
v___x_881_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_877_, v___x_878_, v___x_879_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_882_;
v_res_882_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1___boxed(lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
return v_res_884_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3(){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_912_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6));
v___x_913_ = l_Lean_addBuiltinDeclarationRanges(v___x_911_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_914_;
v_res_914_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___boxed(lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
return v_res_916_;
}
}
lean_object* l_Lean_Parser_Attr_recursor_formatter(lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((lean_object*)(l_Lean_Parser_Attr_recursor_formatter___closed__0));
v___x_941_ = ((lean_object*)(l_Lean_Parser_Attr_recursor_formatter___closed__3));
v___x_942_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_940_, v___x_941_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_942_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_recursor_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_935_ = stack[0].m_obj;
lean_object* v_a_936_ = stack[1].m_obj;
lean_object* v_a_937_ = stack[2].m_obj;
lean_object* v_a_938_ = stack[3].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_Lean_Parser_Attr_recursor_formatter(v_a_935_, v_a_936_, v_a_937_, v_a_938_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_formatter___boxed(lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Parser_Attr_recursor_formatter(v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_949_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7(){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_957_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_958_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_959_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0));
v___x_960_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_recursor_formatter___boxed), 5, 0);
v___x_961_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_957_, v___x_958_, v___x_959_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_962_;
v_res_962_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___boxed(lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
return v_res_964_;
}
}
lean_object* l_Lean_Parser_Attr_recursor_parenthesizer(lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = ((lean_object*)(l_Lean_Parser_Attr_recursor_parenthesizer___closed__0));
v___x_989_ = ((lean_object*)(l_Lean_Parser_Attr_recursor_parenthesizer___closed__3));
v___x_990_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_988_, v___x_989_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_990_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_recursor_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_983_ = stack[0].m_obj;
lean_object* v_a_984_ = stack[1].m_obj;
lean_object* v_a_985_ = stack[2].m_obj;
lean_object* v_a_986_ = stack[3].m_obj;
lean_object* v_res_991_;
v_res_991_ = l_Lean_Parser_Attr_recursor_parenthesizer(v_a_983_, v_a_984_, v_a_985_, v_a_986_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_parenthesizer___boxed(lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Parser_Attr_recursor_parenthesizer(v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
return v_res_997_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11(){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1005_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1006_ = ((lean_object*)(l_Lean_Parser_Attr_recursor___closed__1));
v___x_1007_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0));
v___x_1008_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_recursor_parenthesizer___boxed), 5, 0);
v___x_1009_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1005_, v___x_1006_, v___x_1007_, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1010_;
v_res_1010_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___boxed(lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
return v_res_1012_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class___closed__2(void){
_start:
{
uint8_t v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1019_ = 0;
v___x_1020_ = 1;
v___x_1021_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1022_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__0));
v___x_1023_ = l_Lean_Parser_mkAntiquot(v___x_1022_, v___x_1021_, v___x_1020_, v___x_1019_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class___closed__3(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__0));
v___x_1025_ = l_Lean_Parser_symbol(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class___closed__4(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = lean_obj_once(&l_Lean_Parser_Attr_class___closed__3, &l_Lean_Parser_Attr_class___closed__3_once, _init_l_Lean_Parser_Attr_class___closed__3);
v___x_1027_ = lean_unsigned_to_nat(1024u);
v___x_1028_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1029_ = l_Lean_Parser_leadingNode(v___x_1028_, v___x_1027_, v___x_1026_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class___closed__5(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l_Lean_Parser_Attr_class___closed__4, &l_Lean_Parser_Attr_class___closed__4_once, _init_l_Lean_Parser_Attr_class___closed__4);
v___x_1031_ = lean_obj_once(&l_Lean_Parser_Attr_class___closed__2, &l_Lean_Parser_Attr_class___closed__2_once, _init_l_Lean_Parser_Attr_class___closed__2);
v___x_1032_ = l_Lean_Parser_withAntiquot(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class___closed__6(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_obj_once(&l_Lean_Parser_Attr_class___closed__5, &l_Lean_Parser_Attr_class___closed__5_once, _init_l_Lean_Parser_Attr_class___closed__5);
v___x_1034_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1035_ = l_Lean_Parser_withCache(v___x_1034_, v___x_1033_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Lean_Parser_Attr_class___closed__6, &l_Lean_Parser_Attr_class___closed__6_once, _init_l_Lean_Parser_Attr_class___closed__6);
return v___x_1036_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1(){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1038_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_1039_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1040_ = l_Lean_Parser_Attr_class;
v___x_1041_ = lean_unsigned_to_nat(1000u);
v___x_1042_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1038_, v___x_1039_, v___x_1040_, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1043_;
v_res_1043_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1___boxed(lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
return v_res_1045_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3(){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1073_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6));
v___x_1074_ = l_Lean_addBuiltinDeclarationRanges(v___x_1072_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1075_;
v_res_1075_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___boxed(lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
return v_res_1077_;
}
}
lean_object* l_Lean_Parser_Attr_class_formatter(lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = ((lean_object*)(l_Lean_Parser_Attr_class_formatter___closed__0));
v___x_1097_ = ((lean_object*)(l_Lean_Parser_Attr_class_formatter___closed__2));
v___x_1098_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1096_, v___x_1097_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1098_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_class_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1091_ = stack[0].m_obj;
lean_object* v_a_1092_ = stack[1].m_obj;
lean_object* v_a_1093_ = stack[2].m_obj;
lean_object* v_a_1094_ = stack[3].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_Lean_Parser_Attr_class_formatter(v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_formatter___boxed(lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Parser_Attr_class_formatter(v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1105_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7(){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1113_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1114_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1115_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0));
v___x_1116_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_class_formatter___boxed), 5, 0);
v___x_1117_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1113_, v___x_1114_, v___x_1115_, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1118_;
v_res_1118_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___boxed(lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
return v_res_1120_;
}
}
lean_object* l_Lean_Parser_Attr_class_parenthesizer(lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((lean_object*)(l_Lean_Parser_Attr_class_parenthesizer___closed__0));
v___x_1140_ = ((lean_object*)(l_Lean_Parser_Attr_class_parenthesizer___closed__2));
v___x_1141_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1139_, v___x_1140_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
return v___x_1141_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_class_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1134_ = stack[0].m_obj;
lean_object* v_a_1135_ = stack[1].m_obj;
lean_object* v_a_1136_ = stack[2].m_obj;
lean_object* v_a_1137_ = stack[3].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l_Lean_Parser_Attr_class_parenthesizer(v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_parenthesizer___boxed(lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Parser_Attr_class_parenthesizer(v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1148_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11(){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1157_ = ((lean_object*)(l_Lean_Parser_Attr_class___closed__1));
v___x_1158_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0));
v___x_1159_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_class_parenthesizer___boxed), 5, 0);
v___x_1160_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1156_, v___x_1157_, v___x_1158_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1161_;
v_res_1161_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___boxed(lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
return v_res_1163_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__2(void){
_start:
{
uint8_t v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1170_ = 0;
v___x_1171_ = 1;
v___x_1172_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1173_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__0));
v___x_1174_ = l_Lean_Parser_mkAntiquot(v___x_1173_, v___x_1172_, v___x_1171_, v___x_1170_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__3(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__0));
v___x_1176_ = l_Lean_Parser_symbol(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__4(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_obj_once(&l_Lean_Parser_Attr_simple___closed__3, &l_Lean_Parser_Attr_simple___closed__3_once, _init_l_Lean_Parser_Attr_simple___closed__3);
v___x_1178_ = l_Lean_Parser_skip;
v___x_1179_ = l_Lean_Parser_andthen(v___x_1178_, v___x_1177_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__5(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__4, &l_Lean_Parser_Attr_instance___closed__4_once, _init_l_Lean_Parser_Attr_instance___closed__4);
v___x_1181_ = l_Lean_Parser_optional(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__6(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__5, &l_Lean_Parser_Attr_instance___closed__5_once, _init_l_Lean_Parser_Attr_instance___closed__5);
v___x_1183_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__3, &l_Lean_Parser_Attr_instance___closed__3_once, _init_l_Lean_Parser_Attr_instance___closed__3);
v___x_1184_ = l_Lean_Parser_andthen(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__7(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1185_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__6, &l_Lean_Parser_Attr_instance___closed__6_once, _init_l_Lean_Parser_Attr_instance___closed__6);
v___x_1186_ = lean_unsigned_to_nat(1024u);
v___x_1187_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1188_ = l_Lean_Parser_leadingNode(v___x_1187_, v___x_1186_, v___x_1185_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__8(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__7, &l_Lean_Parser_Attr_instance___closed__7_once, _init_l_Lean_Parser_Attr_instance___closed__7);
v___x_1190_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__2, &l_Lean_Parser_Attr_instance___closed__2_once, _init_l_Lean_Parser_Attr_instance___closed__2);
v___x_1191_ = l_Lean_Parser_withAntiquot(v___x_1190_, v___x_1189_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance___closed__9(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__8, &l_Lean_Parser_Attr_instance___closed__8_once, _init_l_Lean_Parser_Attr_instance___closed__8);
v___x_1193_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1194_ = l_Lean_Parser_withCache(v___x_1193_, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__9, &l_Lean_Parser_Attr_instance___closed__9_once, _init_l_Lean_Parser_Attr_instance___closed__9);
return v___x_1195_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_1198_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1199_ = l_Lean_Parser_Attr_instance;
v___x_1200_ = lean_unsigned_to_nat(1000u);
v___x_1201_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1202_;
v_res_1202_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1___boxed(lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
return v_res_1204_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3(){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1232_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6));
v___x_1233_ = l_Lean_addBuiltinDeclarationRanges(v___x_1231_, v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1234_;
v_res_1234_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___boxed(lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
return v_res_1236_;
}
}
lean_object* l_Lean_Parser_Attr_instance_formatter(lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((lean_object*)(l_Lean_Parser_Attr_instance_formatter___closed__0));
v___x_1264_ = ((lean_object*)(l_Lean_Parser_Attr_instance_formatter___closed__5));
v___x_1265_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1263_, v___x_1264_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_instance_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1258_ = stack[0].m_obj;
lean_object* v_a_1259_ = stack[1].m_obj;
lean_object* v_a_1260_ = stack[2].m_obj;
lean_object* v_a_1261_ = stack[3].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l_Lean_Parser_Attr_instance_formatter(v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_formatter___boxed(lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Parser_Attr_instance_formatter(v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1272_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7(){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1280_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1281_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1282_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0));
v___x_1283_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_instance_formatter___boxed), 5, 0);
v___x_1284_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1280_, v___x_1281_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1285_;
v_res_1285_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___boxed(lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
return v_res_1287_;
}
}
lean_object* l_Lean_Parser_Attr_instance_parenthesizer(lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((lean_object*)(l_Lean_Parser_Attr_instance_parenthesizer___closed__0));
v___x_1315_ = ((lean_object*)(l_Lean_Parser_Attr_instance_parenthesizer___closed__5));
v___x_1316_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1314_, v___x_1315_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1316_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_instance_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1309_ = stack[0].m_obj;
lean_object* v_a_1310_ = stack[1].m_obj;
lean_object* v_a_1311_ = stack[2].m_obj;
lean_object* v_a_1312_ = stack[3].m_obj;
lean_object* v_res_1317_;
v_res_1317_ = l_Lean_Parser_Attr_instance_parenthesizer(v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
stack->m_obj
 = v_res_1317_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_parenthesizer___boxed(lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Parser_Attr_instance_parenthesizer(v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1323_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11(){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1331_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1332_ = ((lean_object*)(l_Lean_Parser_Attr_instance___closed__1));
v___x_1333_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0));
v___x_1334_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_instance_parenthesizer___boxed), 5, 0);
v___x_1335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1331_, v___x_1332_, v___x_1333_, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1336_;
v_res_1336_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___boxed(lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
return v_res_1338_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance___closed__2(void){
_start:
{
uint8_t v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1345_ = 0;
v___x_1346_ = 1;
v___x_1347_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1348_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__0));
v___x_1349_ = l_Lean_Parser_mkAntiquot(v___x_1348_, v___x_1347_, v___x_1346_, v___x_1345_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance___closed__3(void){
_start:
{
uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = 0;
v___x_1351_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__0));
v___x_1352_ = l_Lean_Parser_nonReservedSymbol(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance___closed__4(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_obj_once(&l_Lean_Parser_Attr_instance___closed__5, &l_Lean_Parser_Attr_instance___closed__5_once, _init_l_Lean_Parser_Attr_instance___closed__5);
v___x_1354_ = lean_obj_once(&l_Lean_Parser_Attr_default__instance___closed__3, &l_Lean_Parser_Attr_default__instance___closed__3_once, _init_l_Lean_Parser_Attr_default__instance___closed__3);
v___x_1355_ = l_Lean_Parser_andthen(v___x_1354_, v___x_1353_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance___closed__5(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = lean_obj_once(&l_Lean_Parser_Attr_default__instance___closed__4, &l_Lean_Parser_Attr_default__instance___closed__4_once, _init_l_Lean_Parser_Attr_default__instance___closed__4);
v___x_1357_ = lean_unsigned_to_nat(1024u);
v___x_1358_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1359_ = l_Lean_Parser_leadingNode(v___x_1358_, v___x_1357_, v___x_1356_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance___closed__6(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_obj_once(&l_Lean_Parser_Attr_default__instance___closed__5, &l_Lean_Parser_Attr_default__instance___closed__5_once, _init_l_Lean_Parser_Attr_default__instance___closed__5);
v___x_1361_ = lean_obj_once(&l_Lean_Parser_Attr_default__instance___closed__2, &l_Lean_Parser_Attr_default__instance___closed__2_once, _init_l_Lean_Parser_Attr_default__instance___closed__2);
v___x_1362_ = l_Lean_Parser_withAntiquot(v___x_1361_, v___x_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance___closed__7(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_obj_once(&l_Lean_Parser_Attr_default__instance___closed__6, &l_Lean_Parser_Attr_default__instance___closed__6_once, _init_l_Lean_Parser_Attr_default__instance___closed__6);
v___x_1364_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1365_ = l_Lean_Parser_withCache(v___x_1364_, v___x_1363_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance(void){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_obj_once(&l_Lean_Parser_Attr_default__instance___closed__7, &l_Lean_Parser_Attr_default__instance___closed__7_once, _init_l_Lean_Parser_Attr_default__instance___closed__7);
return v___x_1366_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1(){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1368_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_1369_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1370_ = l_Lean_Parser_Attr_default__instance;
v___x_1371_ = lean_unsigned_to_nat(1000u);
v___x_1372_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1368_, v___x_1369_, v___x_1370_, v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1373_;
v_res_1373_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
stack->m_obj
 = v_res_1373_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1___boxed(lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
return v_res_1375_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3(){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1403_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6));
v___x_1404_ = l_Lean_addBuiltinDeclarationRanges(v___x_1402_, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1405_;
v_res_1405_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
return v_res_1407_;
}
}
lean_object* l_Lean_Parser_Attr_default__instance_formatter(lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance_formatter___closed__0));
v___x_1432_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance_formatter___closed__3));
v___x_1433_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1431_, v___x_1432_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
return v___x_1433_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_default__instance_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1426_ = stack[0].m_obj;
lean_object* v_a_1427_ = stack[1].m_obj;
lean_object* v_a_1428_ = stack[2].m_obj;
lean_object* v_a_1429_ = stack[3].m_obj;
lean_object* v_res_1434_;
v_res_1434_ = l_Lean_Parser_Attr_default__instance_formatter(v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_formatter___boxed(lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Parser_Attr_default__instance_formatter(v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1440_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7(){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1448_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1449_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1450_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0));
v___x_1451_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_default__instance_formatter___boxed), 5, 0);
v___x_1452_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1448_, v___x_1449_, v___x_1450_, v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1453_;
v_res_1453_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___boxed(lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
return v_res_1455_;
}
}
lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer(lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0));
v___x_1480_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3));
v___x_1481_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1479_, v___x_1480_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
return v___x_1481_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_default__instance_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1474_ = stack[0].m_obj;
lean_object* v_a_1475_ = stack[1].m_obj;
lean_object* v_a_1476_ = stack[2].m_obj;
lean_object* v_a_1477_ = stack[3].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_Lean_Parser_Attr_default__instance_parenthesizer(v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer___boxed(lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Parser_Attr_default__instance_parenthesizer(v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1488_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11(){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1496_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1497_ = ((lean_object*)(l_Lean_Parser_Attr_default__instance___closed__1));
v___x_1498_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0));
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_default__instance_parenthesizer___boxed), 5, 0);
v___x_1500_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1496_, v___x_1497_, v___x_1498_, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1501_;
v_res_1501_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
stack->m_obj
 = v_res_1501_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___boxed(lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
return v_res_1503_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__2(void){
_start:
{
uint8_t v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1510_ = 0;
v___x_1511_ = 1;
v___x_1512_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1513_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__0));
v___x_1514_ = l_Lean_Parser_mkAntiquot(v___x_1513_, v___x_1512_, v___x_1511_, v___x_1510_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__3(void){
_start:
{
uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = 0;
v___x_1516_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__0));
v___x_1517_ = l_Lean_Parser_nonReservedSymbol(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__4(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = l_Lean_Parser_numLit;
v___x_1519_ = l_Lean_Parser_ident;
v___x_1520_ = l_Lean_Parser_orelse(v___x_1519_, v___x_1518_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__5(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__4, &l_Lean_Parser_Attr_specialize___closed__4_once, _init_l_Lean_Parser_Attr_specialize___closed__4);
v___x_1522_ = l_Lean_Parser_skip;
v___x_1523_ = l_Lean_Parser_andthen(v___x_1522_, v___x_1521_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__6(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__5, &l_Lean_Parser_Attr_specialize___closed__5_once, _init_l_Lean_Parser_Attr_specialize___closed__5);
v___x_1525_ = l_Lean_Parser_many(v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__7(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__6, &l_Lean_Parser_Attr_specialize___closed__6_once, _init_l_Lean_Parser_Attr_specialize___closed__6);
v___x_1527_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__3, &l_Lean_Parser_Attr_specialize___closed__3_once, _init_l_Lean_Parser_Attr_specialize___closed__3);
v___x_1528_ = l_Lean_Parser_andthen(v___x_1527_, v___x_1526_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__8(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__7, &l_Lean_Parser_Attr_specialize___closed__7_once, _init_l_Lean_Parser_Attr_specialize___closed__7);
v___x_1530_ = lean_unsigned_to_nat(1024u);
v___x_1531_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1532_ = l_Lean_Parser_leadingNode(v___x_1531_, v___x_1530_, v___x_1529_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__9(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__8, &l_Lean_Parser_Attr_specialize___closed__8_once, _init_l_Lean_Parser_Attr_specialize___closed__8);
v___x_1534_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__2, &l_Lean_Parser_Attr_specialize___closed__2_once, _init_l_Lean_Parser_Attr_specialize___closed__2);
v___x_1535_ = l_Lean_Parser_withAntiquot(v___x_1534_, v___x_1533_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize___closed__10(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__9, &l_Lean_Parser_Attr_specialize___closed__9_once, _init_l_Lean_Parser_Attr_specialize___closed__9);
v___x_1537_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1538_ = l_Lean_Parser_withCache(v___x_1537_, v___x_1536_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize(void){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_obj_once(&l_Lean_Parser_Attr_specialize___closed__10, &l_Lean_Parser_Attr_specialize___closed__10_once, _init_l_Lean_Parser_Attr_specialize___closed__10);
return v___x_1539_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1(){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_1542_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1543_ = l_Lean_Parser_Attr_specialize;
v___x_1544_ = lean_unsigned_to_nat(1000u);
v___x_1545_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1541_, v___x_1542_, v___x_1543_, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1546_;
v_res_1546_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1___boxed(lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
return v_res_1548_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3(){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1576_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6));
v___x_1577_ = l_Lean_addBuiltinDeclarationRanges(v___x_1575_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1578_;
v_res_1578_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___boxed(lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
return v_res_1580_;
}
}
lean_object* l_Lean_Parser_Attr_specialize_formatter(lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((lean_object*)(l_Lean_Parser_Attr_specialize_formatter___closed__0));
v___x_1613_ = ((lean_object*)(l_Lean_Parser_Attr_specialize_formatter___closed__6));
v___x_1614_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1612_, v___x_1613_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_specialize_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1607_ = stack[0].m_obj;
lean_object* v_a_1608_ = stack[1].m_obj;
lean_object* v_a_1609_ = stack[2].m_obj;
lean_object* v_a_1610_ = stack[3].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l_Lean_Parser_Attr_specialize_formatter(v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_formatter___boxed(lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Parser_Attr_specialize_formatter(v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1621_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7(){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1629_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1630_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1631_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0));
v___x_1632_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_specialize_formatter___boxed), 5, 0);
v___x_1633_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1629_, v___x_1630_, v___x_1631_, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1634_;
v_res_1634_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___boxed(lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
return v_res_1636_;
}
}
lean_object* l_Lean_Parser_Attr_specialize_parenthesizer(lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = ((lean_object*)(l_Lean_Parser_Attr_specialize_parenthesizer___closed__0));
v___x_1669_ = ((lean_object*)(l_Lean_Parser_Attr_specialize_parenthesizer___closed__6));
v___x_1670_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1668_, v___x_1669_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1670_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_specialize_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1663_ = stack[0].m_obj;
lean_object* v_a_1664_ = stack[1].m_obj;
lean_object* v_a_1665_ = stack[2].m_obj;
lean_object* v_a_1666_ = stack[3].m_obj;
lean_object* v_res_1671_;
v_res_1671_ = l_Lean_Parser_Attr_specialize_parenthesizer(v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
stack->m_obj
 = v_res_1671_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_parenthesizer___boxed(lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Parser_Attr_specialize_parenthesizer(v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1677_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11(){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1685_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1686_ = ((lean_object*)(l_Lean_Parser_Attr_specialize___closed__1));
v___x_1687_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0));
v___x_1688_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_specialize_parenthesizer___boxed), 5, 0);
v___x_1689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1685_, v___x_1686_, v___x_1687_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1690_;
v_res_1690_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___boxed(lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
return v_res_1692_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__2(void){
_start:
{
uint8_t v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1699_ = 0;
v___x_1700_ = 1;
v___x_1701_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__1));
v___x_1702_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__0));
v___x_1703_ = l_Lean_Parser_mkAntiquot(v___x_1702_, v___x_1701_, v___x_1700_, v___x_1699_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__3(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = l_Lean_Parser_skip;
v___x_1705_ = l_Lean_Parser_ident;
v___x_1706_ = l_Lean_Parser_andthen(v___x_1705_, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__4(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__3, &l_Lean_Parser_Attr_externEntry___closed__3_once, _init_l_Lean_Parser_Attr_externEntry___closed__3);
v___x_1708_ = l_Lean_Parser_optional(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__6(void){
_start:
{
uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = 0;
v___x_1711_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__5));
v___x_1712_ = l_Lean_Parser_nonReservedSymbol(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__7(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__6, &l_Lean_Parser_Attr_externEntry___closed__6_once, _init_l_Lean_Parser_Attr_externEntry___closed__6);
v___x_1714_ = l_Lean_Parser_optional(v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__8(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = l_Lean_Parser_strLit;
v___x_1716_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__7, &l_Lean_Parser_Attr_externEntry___closed__7_once, _init_l_Lean_Parser_Attr_externEntry___closed__7);
v___x_1717_ = l_Lean_Parser_andthen(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__9(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__8, &l_Lean_Parser_Attr_externEntry___closed__8_once, _init_l_Lean_Parser_Attr_externEntry___closed__8);
v___x_1719_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__4, &l_Lean_Parser_Attr_externEntry___closed__4_once, _init_l_Lean_Parser_Attr_externEntry___closed__4);
v___x_1720_ = l_Lean_Parser_andthen(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__10(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__9, &l_Lean_Parser_Attr_externEntry___closed__9_once, _init_l_Lean_Parser_Attr_externEntry___closed__9);
v___x_1722_ = lean_unsigned_to_nat(1024u);
v___x_1723_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__1));
v___x_1724_ = l_Lean_Parser_leadingNode(v___x_1723_, v___x_1722_, v___x_1721_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__11(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__10, &l_Lean_Parser_Attr_externEntry___closed__10_once, _init_l_Lean_Parser_Attr_externEntry___closed__10);
v___x_1726_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__2, &l_Lean_Parser_Attr_externEntry___closed__2_once, _init_l_Lean_Parser_Attr_externEntry___closed__2);
v___x_1727_ = l_Lean_Parser_withAntiquot(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry___closed__12(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__11, &l_Lean_Parser_Attr_externEntry___closed__11_once, _init_l_Lean_Parser_Attr_externEntry___closed__11);
v___x_1729_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__1));
v___x_1730_ = l_Lean_Parser_withCache(v___x_1729_, v___x_1728_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry(void){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_obj_once(&l_Lean_Parser_Attr_externEntry___closed__12, &l_Lean_Parser_Attr_externEntry___closed__12_once, _init_l_Lean_Parser_Attr_externEntry___closed__12);
return v___x_1731_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__2(void){
_start:
{
uint8_t v___x_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1738_ = 0;
v___x_1739_ = 1;
v___x_1740_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1741_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__0));
v___x_1742_ = l_Lean_Parser_mkAntiquot(v___x_1741_, v___x_1740_, v___x_1739_, v___x_1738_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__3(void){
_start:
{
uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = 0;
v___x_1744_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__0));
v___x_1745_ = l_Lean_Parser_nonReservedSymbol(v___x_1744_, v___x_1743_);
return v___x_1745_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__4(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = l_Lean_Parser_Attr_externEntry;
v___x_1747_ = l_Lean_Parser_skip;
v___x_1748_ = l_Lean_Parser_andthen(v___x_1747_, v___x_1746_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__5(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__4, &l_Lean_Parser_Attr_extern___closed__4_once, _init_l_Lean_Parser_Attr_extern___closed__4);
v___x_1750_ = l_Lean_Parser_many(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__6(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__5, &l_Lean_Parser_Attr_extern___closed__5_once, _init_l_Lean_Parser_Attr_extern___closed__5);
v___x_1752_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__3, &l_Lean_Parser_Attr_extern___closed__3_once, _init_l_Lean_Parser_Attr_extern___closed__3);
v___x_1753_ = l_Lean_Parser_andthen(v___x_1752_, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__7(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__6, &l_Lean_Parser_Attr_extern___closed__6_once, _init_l_Lean_Parser_Attr_extern___closed__6);
v___x_1755_ = lean_unsigned_to_nat(1024u);
v___x_1756_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1757_ = l_Lean_Parser_leadingNode(v___x_1756_, v___x_1755_, v___x_1754_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__8(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__7, &l_Lean_Parser_Attr_extern___closed__7_once, _init_l_Lean_Parser_Attr_extern___closed__7);
v___x_1759_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__2, &l_Lean_Parser_Attr_extern___closed__2_once, _init_l_Lean_Parser_Attr_extern___closed__2);
v___x_1760_ = l_Lean_Parser_withAntiquot(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern___closed__9(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__8, &l_Lean_Parser_Attr_extern___closed__8_once, _init_l_Lean_Parser_Attr_extern___closed__8);
v___x_1762_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1763_ = l_Lean_Parser_withCache(v___x_1762_, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern(void){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_obj_once(&l_Lean_Parser_Attr_extern___closed__9, &l_Lean_Parser_Attr_extern___closed__9_once, _init_l_Lean_Parser_Attr_extern___closed__9);
return v___x_1764_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1(){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_1767_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1768_ = l_Lean_Parser_Attr_extern;
v___x_1769_ = lean_unsigned_to_nat(1000u);
v___x_1770_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_1766_, v___x_1767_, v___x_1768_, v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1771_;
v_res_1771_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
stack->m_obj
 = v_res_1771_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1___boxed(lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
return v_res_1773_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3(){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1801_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6));
v___x_1802_ = l_Lean_addBuiltinDeclarationRanges(v___x_1800_, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1803_;
v_res_1803_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
stack->m_obj
 = v_res_1803_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___boxed(lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
return v_res_1805_;
}
}
lean_object* l_Lean_Parser_Attr_externEntry_formatter(lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry_formatter___closed__0));
v___x_1841_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry_formatter___closed__8));
v___x_1842_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1840_, v___x_1841_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1842_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_externEntry_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1835_ = stack[0].m_obj;
lean_object* v_a_1836_ = stack[1].m_obj;
lean_object* v_a_1837_ = stack[2].m_obj;
lean_object* v_a_1838_ = stack[3].m_obj;
lean_object* v_res_1843_;
v_res_1843_ = l_Lean_Parser_Attr_externEntry_formatter(v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
stack->m_obj
 = v_res_1843_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_formatter___boxed(lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_Parser_Attr_externEntry_formatter(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1849_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7(){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1857_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1858_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__1));
v___x_1859_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0));
v___x_1860_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_formatter___boxed), 5, 0);
v___x_1861_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1857_, v___x_1858_, v___x_1859_, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1862_;
v_res_1862_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
stack->m_obj
 = v_res_1862_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
return v_res_1864_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_formatter___closed__2(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_formatter___boxed), 5, 0);
v___f_1877_ = ((lean_object*)(l_Lean_Parser_Attr_simple_formatter___closed__0));
v___x_1878_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1878_, 0, v___f_1877_);
lean_closure_set(v___x_1878_, 1, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_formatter___closed__3(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_obj_once(&l_Lean_Parser_Attr_extern_formatter___closed__2, &l_Lean_Parser_Attr_extern_formatter___closed__2_once, _init_l_Lean_Parser_Attr_extern_formatter___closed__2);
v___x_1880_ = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter___boxed), 6, 1);
lean_closure_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_formatter___closed__4(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_obj_once(&l_Lean_Parser_Attr_extern_formatter___closed__3, &l_Lean_Parser_Attr_extern_formatter___closed__3_once, _init_l_Lean_Parser_Attr_extern_formatter___closed__3);
v___x_1882_ = ((lean_object*)(l_Lean_Parser_Attr_extern_formatter___closed__1));
v___x_1883_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1883_, 0, v___x_1882_);
lean_closure_set(v___x_1883_, 1, v___x_1881_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_formatter___closed__5(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1884_ = lean_obj_once(&l_Lean_Parser_Attr_extern_formatter___closed__4, &l_Lean_Parser_Attr_extern_formatter___closed__4_once, _init_l_Lean_Parser_Attr_extern_formatter___closed__4);
v___x_1885_ = lean_unsigned_to_nat(1024u);
v___x_1886_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1887_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1887_, 0, v___x_1886_);
lean_closure_set(v___x_1887_, 1, v___x_1885_);
lean_closure_set(v___x_1887_, 2, v___x_1884_);
return v___x_1887_;
}
}
lean_object* l_Lean_Parser_Attr_extern_formatter(lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((lean_object*)(l_Lean_Parser_Attr_extern_formatter___closed__0));
v___x_1894_ = lean_obj_once(&l_Lean_Parser_Attr_extern_formatter___closed__5, &l_Lean_Parser_Attr_extern_formatter___closed__5_once, _init_l_Lean_Parser_Attr_extern_formatter___closed__5);
v___x_1895_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1893_, v___x_1894_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_1895_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_extern_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1888_ = stack[0].m_obj;
lean_object* v_a_1889_ = stack[1].m_obj;
lean_object* v_a_1890_ = stack[2].m_obj;
lean_object* v_a_1891_ = stack[3].m_obj;
lean_object* v_res_1896_;
v_res_1896_ = l_Lean_Parser_Attr_extern_formatter(v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
stack->m_obj
 = v_res_1896_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_formatter___boxed(lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Parser_Attr_extern_formatter(v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1902_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11(){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1910_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1911_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1912_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0));
v___x_1913_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_extern_formatter___boxed), 5, 0);
v___x_1914_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1910_, v___x_1911_, v___x_1912_, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1915_;
v_res_1915_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___boxed(lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
return v_res_1917_;
}
}
lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer(lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0));
v___x_1953_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8));
v___x_1954_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1952_, v___x_1953_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_externEntry_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1947_ = stack[0].m_obj;
lean_object* v_a_1948_ = stack[1].m_obj;
lean_object* v_a_1949_ = stack[2].m_obj;
lean_object* v_a_1950_ = stack[3].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Lean_Parser_Attr_externEntry_parenthesizer(v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
stack->m_obj
 = v_res_1955_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer___boxed(lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Parser_Attr_externEntry_parenthesizer(v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1961_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15(){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1969_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1970_ = ((lean_object*)(l_Lean_Parser_Attr_externEntry___closed__1));
v___x_1971_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0));
v___x_1972_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_parenthesizer___boxed), 5, 0);
v___x_1973_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1969_, v___x_1970_, v___x_1971_, v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1974_;
v_res_1974_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
stack->m_obj
 = v_res_1974_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___boxed(lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_parenthesizer___boxed), 5, 0);
v___x_1989_ = ((lean_object*)(l_Lean_Parser_Attr_simple_parenthesizer___closed__2));
v___x_1990_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1990_, 0, v___x_1989_);
lean_closure_set(v___x_1990_, 1, v___x_1988_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_obj_once(&l_Lean_Parser_Attr_extern_parenthesizer___closed__2, &l_Lean_Parser_Attr_extern_parenthesizer___closed__2_once, _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__2);
v___x_1992_ = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_obj_once(&l_Lean_Parser_Attr_extern_parenthesizer___closed__3, &l_Lean_Parser_Attr_extern_parenthesizer___closed__3_once, _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__3);
v___x_1994_ = ((lean_object*)(l_Lean_Parser_Attr_extern_parenthesizer___closed__1));
v___x_1995_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1995_, 0, v___x_1994_);
lean_closure_set(v___x_1995_, 1, v___x_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_obj_once(&l_Lean_Parser_Attr_extern_parenthesizer___closed__4, &l_Lean_Parser_Attr_extern_parenthesizer___closed__4_once, _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__4);
v___x_1997_ = lean_unsigned_to_nat(1024u);
v___x_1998_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_1999_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1999_, 0, v___x_1998_);
lean_closure_set(v___x_1999_, 1, v___x_1997_);
lean_closure_set(v___x_1999_, 2, v___x_1996_);
return v___x_1999_;
}
}
lean_object* l_Lean_Parser_Attr_extern_parenthesizer(lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = ((lean_object*)(l_Lean_Parser_Attr_extern_parenthesizer___closed__0));
v___x_2006_ = lean_obj_once(&l_Lean_Parser_Attr_extern_parenthesizer___closed__5, &l_Lean_Parser_Attr_extern_parenthesizer___closed__5_once, _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__5);
v___x_2007_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2005_, v___x_2006_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
return v___x_2007_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_extern_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2000_ = stack[0].m_obj;
lean_object* v_a_2001_ = stack[1].m_obj;
lean_object* v_a_2002_ = stack[2].m_obj;
lean_object* v_a_2003_ = stack[3].m_obj;
lean_object* v_res_2008_;
v_res_2008_ = l_Lean_Parser_Attr_extern_parenthesizer(v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
stack->m_obj
 = v_res_2008_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_parenthesizer___boxed(lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Parser_Attr_extern_parenthesizer(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2014_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19(){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2022_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2023_ = ((lean_object*)(l_Lean_Parser_Attr_extern___closed__1));
v___x_2024_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0));
v___x_2025_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_extern_parenthesizer___boxed), 5, 0);
v___x_2026_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2022_, v___x_2023_, v___x_2024_, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2027_;
v_res_2027_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___boxed(lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
return v_res_2029_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__2(void){
_start:
{
uint8_t v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2036_ = 0;
v___x_2037_ = 1;
v___x_2038_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2039_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__0));
v___x_2040_ = l_Lean_Parser_mkAntiquot(v___x_2039_, v___x_2038_, v___x_2037_, v___x_2036_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__3(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__0));
v___x_2042_ = l_Lean_Parser_symbol(v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__4(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = l_Lean_Parser_ident;
v___x_2044_ = l_Lean_Parser_skip;
v___x_2045_ = l_Lean_Parser_andthen(v___x_2044_, v___x_2043_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__5(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__4, &l_Lean_Parser_Attr_tactic__alt___closed__4_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__4);
v___x_2047_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__3, &l_Lean_Parser_Attr_tactic__alt___closed__3_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__3);
v___x_2048_ = l_Lean_Parser_andthen(v___x_2047_, v___x_2046_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__6(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2049_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__5, &l_Lean_Parser_Attr_tactic__alt___closed__5_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__5);
v___x_2050_ = lean_unsigned_to_nat(1024u);
v___x_2051_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2052_ = l_Lean_Parser_leadingNode(v___x_2051_, v___x_2050_, v___x_2049_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__7(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__6, &l_Lean_Parser_Attr_tactic__alt___closed__6_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__6);
v___x_2054_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__2, &l_Lean_Parser_Attr_tactic__alt___closed__2_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__2);
v___x_2055_ = l_Lean_Parser_withAntiquot(v___x_2054_, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt___closed__8(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__7, &l_Lean_Parser_Attr_tactic__alt___closed__7_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__7);
v___x_2057_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2058_ = l_Lean_Parser_withCache(v___x_2057_, v___x_2056_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt(void){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__8, &l_Lean_Parser_Attr_tactic__alt___closed__8_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__8);
return v___x_2059_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1(){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_2062_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2063_ = l_Lean_Parser_Attr_tactic__alt;
v___x_2064_ = lean_unsigned_to_nat(1000u);
v___x_2065_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_2061_, v___x_2062_, v___x_2063_, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2066_;
v_res_2066_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1___boxed(lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
return v_res_2068_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3(){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2072_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0));
v___x_2073_ = l_Lean_addBuiltinDocString(v___x_2071_, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2074_;
v_res_2074_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
stack->m_obj
 = v_res_2074_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___boxed(lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
return v_res_2076_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5(){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2104_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6));
v___x_2105_ = l_Lean_addBuiltinDeclarationRanges(v___x_2103_, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2106_;
v_res_2106_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
stack->m_obj
 = v_res_2106_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___boxed(lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
return v_res_2108_;
}
}
lean_object* l_Lean_Parser_Attr_tactic__alt_formatter(lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt_formatter___closed__0));
v___x_2134_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt_formatter___closed__4));
v___x_2135_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2133_, v___x_2134_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
return v___x_2135_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_tactic__alt_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2128_ = stack[0].m_obj;
lean_object* v_a_2129_ = stack[1].m_obj;
lean_object* v_a_2130_ = stack[2].m_obj;
lean_object* v_a_2131_ = stack[3].m_obj;
lean_object* v_res_2136_;
v_res_2136_ = l_Lean_Parser_Attr_tactic__alt_formatter(v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
stack->m_obj
 = v_res_2136_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_formatter___boxed(lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Parser_Attr_tactic__alt_formatter(v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
return v_res_2142_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9(){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2150_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2151_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2152_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0));
v___x_2153_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__alt_formatter___boxed), 5, 0);
v___x_2154_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2150_, v___x_2151_, v___x_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2155_;
v_res_2155_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___boxed(lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
return v_res_2157_;
}
}
lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer(lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0));
v___x_2183_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4));
v___x_2184_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2182_, v___x_2183_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2184_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_tactic__alt_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2177_ = stack[0].m_obj;
lean_object* v_a_2178_ = stack[1].m_obj;
lean_object* v_a_2179_ = stack[2].m_obj;
lean_object* v_a_2180_ = stack[3].m_obj;
lean_object* v_res_2185_;
v_res_2185_ = l_Lean_Parser_Attr_tactic__alt_parenthesizer(v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
stack->m_obj
 = v_res_2185_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer___boxed(lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Parser_Attr_tactic__alt_parenthesizer(v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
return v_res_2191_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13(){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2199_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2200_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__alt___closed__1));
v___x_2201_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0));
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__alt_parenthesizer___boxed), 5, 0);
v___x_2203_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2199_, v___x_2200_, v___x_2201_, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2204_;
v_res_2204_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
stack->m_obj
 = v_res_2204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___boxed(lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
return v_res_2206_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__2(void){
_start:
{
uint8_t v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2213_ = 0;
v___x_2214_ = 1;
v___x_2215_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2216_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__0));
v___x_2217_ = l_Lean_Parser_mkAntiquot(v___x_2216_, v___x_2215_, v___x_2214_, v___x_2213_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__3(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__0));
v___x_2219_ = l_Lean_Parser_symbol(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__4(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__alt___closed__4, &l_Lean_Parser_Attr_tactic__alt___closed__4_once, _init_l_Lean_Parser_Attr_tactic__alt___closed__4);
v___x_2221_ = l_Lean_Parser_many1(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__5(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__4, &l_Lean_Parser_Attr_tactic__tag___closed__4_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__4);
v___x_2223_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__3, &l_Lean_Parser_Attr_tactic__tag___closed__3_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__3);
v___x_2224_ = l_Lean_Parser_andthen(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__6(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__5, &l_Lean_Parser_Attr_tactic__tag___closed__5_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__5);
v___x_2226_ = lean_unsigned_to_nat(1024u);
v___x_2227_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2228_ = l_Lean_Parser_leadingNode(v___x_2227_, v___x_2226_, v___x_2225_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__7(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__6, &l_Lean_Parser_Attr_tactic__tag___closed__6_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__6);
v___x_2230_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__2, &l_Lean_Parser_Attr_tactic__tag___closed__2_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__2);
v___x_2231_ = l_Lean_Parser_withAntiquot(v___x_2230_, v___x_2229_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag___closed__8(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__7, &l_Lean_Parser_Attr_tactic__tag___closed__7_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__7);
v___x_2233_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2234_ = l_Lean_Parser_withCache(v___x_2233_, v___x_2232_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag(void){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__tag___closed__8, &l_Lean_Parser_Attr_tactic__tag___closed__8_once, _init_l_Lean_Parser_Attr_tactic__tag___closed__8);
return v___x_2235_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1(){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_2238_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2239_ = l_Lean_Parser_Attr_tactic__tag;
v___x_2240_ = lean_unsigned_to_nat(1000u);
v___x_2241_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_2237_, v___x_2238_, v___x_2239_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2242_;
v_res_2242_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
stack->m_obj
 = v_res_2242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1___boxed(lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
return v_res_2244_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3(){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2248_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0));
v___x_2249_ = l_Lean_addBuiltinDocString(v___x_2247_, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2250_;
v_res_2250_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
stack->m_obj
 = v_res_2250_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___boxed(lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
return v_res_2252_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5(){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2280_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6));
v___x_2281_ = l_Lean_addBuiltinDeclarationRanges(v___x_2279_, v___x_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2282_;
v_res_2282_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
stack->m_obj
 = v_res_2282_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___boxed(lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
return v_res_2284_;
}
}
lean_object* l_Lean_Parser_Attr_tactic__tag_formatter(lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag_formatter___closed__0));
v___x_2309_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag_formatter___closed__4));
v___x_2310_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2308_, v___x_2309_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2310_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_tactic__tag_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2303_ = stack[0].m_obj;
lean_object* v_a_2304_ = stack[1].m_obj;
lean_object* v_a_2305_ = stack[2].m_obj;
lean_object* v_a_2306_ = stack[3].m_obj;
lean_object* v_res_2311_;
v_res_2311_ = l_Lean_Parser_Attr_tactic__tag_formatter(v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
stack->m_obj
 = v_res_2311_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_formatter___boxed(lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Parser_Attr_tactic__tag_formatter(v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
return v_res_2317_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9(){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2325_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2326_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2327_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0));
v___x_2328_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__tag_formatter___boxed), 5, 0);
v___x_2329_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2325_, v___x_2326_, v___x_2327_, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2330_;
v_res_2330_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
stack->m_obj
 = v_res_2330_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___boxed(lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
return v_res_2332_;
}
}
lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer(lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0));
v___x_2357_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4));
v___x_2358_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2356_, v___x_2357_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v___x_2358_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_tactic__tag_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2351_ = stack[0].m_obj;
lean_object* v_a_2352_ = stack[1].m_obj;
lean_object* v_a_2353_ = stack[2].m_obj;
lean_object* v_a_2354_ = stack[3].m_obj;
lean_object* v_res_2359_;
v_res_2359_ = l_Lean_Parser_Attr_tactic__tag_parenthesizer(v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
stack->m_obj
 = v_res_2359_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer___boxed(lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Parser_Attr_tactic__tag_parenthesizer(v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
return v_res_2365_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13(){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2373_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2374_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__tag___closed__1));
v___x_2375_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0));
v___x_2376_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__tag_parenthesizer___boxed), 5, 0);
v___x_2377_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2373_, v___x_2374_, v___x_2375_, v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2378_;
v_res_2378_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
stack->m_obj
 = v_res_2378_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___boxed(lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
return v_res_2380_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__2(void){
_start:
{
uint8_t v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2387_ = 0;
v___x_2388_ = 1;
v___x_2389_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2390_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__0));
v___x_2391_ = l_Lean_Parser_mkAntiquot(v___x_2390_, v___x_2389_, v___x_2388_, v___x_2387_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__3(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__0));
v___x_2393_ = l_Lean_Parser_symbol(v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__4(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = l_Lean_Parser_strLit;
v___x_2395_ = l_Lean_Parser_ident;
v___x_2396_ = l_Lean_Parser_orelse(v___x_2395_, v___x_2394_);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__5(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__4, &l_Lean_Parser_Attr_tactic__name___closed__4_once, _init_l_Lean_Parser_Attr_tactic__name___closed__4);
v___x_2398_ = l_Lean_Parser_skip;
v___x_2399_ = l_Lean_Parser_andthen(v___x_2398_, v___x_2397_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__6(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__5, &l_Lean_Parser_Attr_tactic__name___closed__5_once, _init_l_Lean_Parser_Attr_tactic__name___closed__5);
v___x_2401_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__3, &l_Lean_Parser_Attr_tactic__name___closed__3_once, _init_l_Lean_Parser_Attr_tactic__name___closed__3);
v___x_2402_ = l_Lean_Parser_andthen(v___x_2401_, v___x_2400_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__7(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2403_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__6, &l_Lean_Parser_Attr_tactic__name___closed__6_once, _init_l_Lean_Parser_Attr_tactic__name___closed__6);
v___x_2404_ = lean_unsigned_to_nat(1024u);
v___x_2405_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2406_ = l_Lean_Parser_leadingNode(v___x_2405_, v___x_2404_, v___x_2403_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__8(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__7, &l_Lean_Parser_Attr_tactic__name___closed__7_once, _init_l_Lean_Parser_Attr_tactic__name___closed__7);
v___x_2408_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__2, &l_Lean_Parser_Attr_tactic__name___closed__2_once, _init_l_Lean_Parser_Attr_tactic__name___closed__2);
v___x_2409_ = l_Lean_Parser_withAntiquot(v___x_2408_, v___x_2407_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name___closed__9(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__8, &l_Lean_Parser_Attr_tactic__name___closed__8_once, _init_l_Lean_Parser_Attr_tactic__name___closed__8);
v___x_2411_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2412_ = l_Lean_Parser_withCache(v___x_2411_, v___x_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__name(void){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_obj_once(&l_Lean_Parser_Attr_tactic__name___closed__9, &l_Lean_Parser_Attr_tactic__name___closed__9_once, _init_l_Lean_Parser_Attr_tactic__name___closed__9);
return v___x_2413_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1(){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2415_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_));
v___x_2416_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2417_ = l_Lean_Parser_Attr_tactic__name;
v___x_2418_ = lean_unsigned_to_nat(1000u);
v___x_2419_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_2415_, v___x_2416_, v___x_2417_, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2420_;
v_res_2420_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
stack->m_obj
 = v_res_2420_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1___boxed(lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
return v_res_2422_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3(){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2426_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0));
v___x_2427_ = l_Lean_addBuiltinDocString(v___x_2425_, v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2428_;
v_res_2428_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
stack->m_obj
 = v_res_2428_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___boxed(lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
return v_res_2430_;
}
}
lean_object* l_Lean_Parser_Attr_tactic__name_formatter(lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name_formatter___closed__0));
v___x_2459_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name_formatter___closed__5));
v___x_2460_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2458_, v___x_2459_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
return v___x_2460_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_tactic__name_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2453_ = stack[0].m_obj;
lean_object* v_a_2454_ = stack[1].m_obj;
lean_object* v_a_2455_ = stack[2].m_obj;
lean_object* v_a_2456_ = stack[3].m_obj;
lean_object* v_res_2461_;
v_res_2461_ = l_Lean_Parser_Attr_tactic__name_formatter(v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name_formatter___boxed(lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Parser_Attr_tactic__name_formatter(v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
return v_res_2467_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7(){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2475_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2476_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2477_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0));
v___x_2478_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__name_formatter___boxed), 5, 0);
v___x_2479_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2475_, v___x_2476_, v___x_2477_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2480_;
v_res_2480_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___boxed(lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
return v_res_2482_;
}
}
lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer(lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0));
v___x_2511_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5));
v___x_2512_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2510_, v___x_2511_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2512_;
}
}
LEAN_EXPORT void l_Lean_Parser_Attr_tactic__name_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2505_ = stack[0].m_obj;
lean_object* v_a_2506_ = stack[1].m_obj;
lean_object* v_a_2507_ = stack[2].m_obj;
lean_object* v_a_2508_ = stack[3].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_Parser_Attr_tactic__name_parenthesizer(v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__name_parenthesizer___boxed(lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Parser_Attr_tactic__name_parenthesizer(v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2519_;
}
}
lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11(){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2527_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2528_ = ((lean_object*)(l_Lean_Parser_Attr_tactic__name___closed__1));
v___x_2529_ = ((lean_object*)(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0));
v___x_2530_ = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__name_parenthesizer___boxed), 5, 0);
v___x_2531_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2527_, v___x_2528_, v___x_2529_, v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2532_;
v_res_2532_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
stack->m_obj
 = v_res_2532_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___boxed(lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
return v_res_2534_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Priority_numPrio = _init_l_Lean_Parser_Priority_numPrio();
lean_mark_persistent(l_Lean_Parser_Priority_numPrio);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_simple = _init_l_Lean_Parser_Attr_simple();
lean_mark_persistent(l_Lean_Parser_Attr_simple);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_macro = _init_l_Lean_Parser_Attr_macro();
lean_mark_persistent(l_Lean_Parser_Attr_macro);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_export = _init_l_Lean_Parser_Attr_export();
lean_mark_persistent(l_Lean_Parser_Attr_export);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_recursor = _init_l_Lean_Parser_Attr_recursor();
lean_mark_persistent(l_Lean_Parser_Attr_recursor);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_class = _init_l_Lean_Parser_Attr_class();
lean_mark_persistent(l_Lean_Parser_Attr_class);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_instance = _init_l_Lean_Parser_Attr_instance();
lean_mark_persistent(l_Lean_Parser_Attr_instance);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_default__instance = _init_l_Lean_Parser_Attr_default__instance();
lean_mark_persistent(l_Lean_Parser_Attr_default__instance);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_specialize = _init_l_Lean_Parser_Attr_specialize();
lean_mark_persistent(l_Lean_Parser_Attr_specialize);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_externEntry = _init_l_Lean_Parser_Attr_externEntry();
lean_mark_persistent(l_Lean_Parser_Attr_externEntry);
l_Lean_Parser_Attr_extern = _init_l_Lean_Parser_Attr_extern();
lean_mark_persistent(l_Lean_Parser_Attr_extern);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_tactic__alt = _init_l_Lean_Parser_Attr_tactic__alt();
lean_mark_persistent(l_Lean_Parser_Attr_tactic__alt);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_tactic__tag = _init_l_Lean_Parser_Attr_tactic__tag();
lean_mark_persistent(l_Lean_Parser_Attr_tactic__tag);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Attr_tactic__name = _init_l_Lean_Parser_Attr_tactic__name();
lean_mark_persistent(l_Lean_Parser_Attr_tactic__name);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
