// Lean compiler output
// Module: Lean.Parser.Tactic
// Imports: public import Lean.Parser.Term public import Lean.Parser.Tactic.Doc public import Std.Tactic.Do.Syntax
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
lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_tacticSeq;
extern lean_object* l_Lean_Parser_Term_syntheticHole;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_hole;
lean_object* l_Lean_Parser_Term_matchAlts(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_hole_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_tacticSeq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_syntheticHole_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_hole_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppDedent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchDiscr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt;
lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
extern lean_object* l_Lean_Parser_Term_matchDiscr;
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchDiscr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_motive;
lean_object* l_Lean_Parser_optional(lean_object*);
extern lean_object* l_Lean_Parser_Term_generalizingParam;
extern lean_object* l_Lean_Parser_leadPrec;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_motive_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_generalizingParam_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_motive_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_errorAtSavedPos(lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_generalizingParam_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppDedent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_tacticSeqBracketed;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticSeqIndentGt"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 96, 154, 40, 0, 37, 199, 17)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeq_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_unknown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l_Lean_Parser_Tactic_unknown___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_unknown___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_unknown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_unknown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_unknown___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_unknown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 186, 215, 255, 42, 124, 128, 137)}};
static const lean_object* l_Lean_Parser_Tactic_unknown___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__2;
static const lean_string_object l_Lean_Parser_Tactic_unknown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "unknown tactic"};
static const lean_object* l_Lean_Parser_Tactic_unknown___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_unknown___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_unknown___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_unknown___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4_value),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_unknown_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_withPosition_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Tactic_unknown_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_formatter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 186, 215, 255, 42, 124, 128, 137)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 70, 177, 213, 33, 170, 221, 209)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_unknown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 186, 215, 255, 42, 124, 128, 137)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 132, 153, 21, 93, 168, 106, 226)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 38, 10, 255, 87, 102, 123, 100)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_matchRhs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_matchRhs___closed__0;
static lean_once_cell_t l_Lean_Parser_Tactic_matchRhs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_matchRhs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs;
static lean_once_cell_t l_Lean_Parser_Tactic_matchAlts___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_matchAlts___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts;
static const lean_string_object l_Lean_Parser_Tactic_match___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Parser_Tactic_match___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_match___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_match___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_match___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_match___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_match___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_match___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 240, 216, 203, 28, 130, 220)}};
static const lean_object* l_Lean_Parser_Tactic_match___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_match___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__2;
static const lean_string_object l_Lean_Parser_Tactic_match___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match "};
static const lean_object* l_Lean_Parser_Tactic_match___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_match___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__6;
static const lean_string_object l_Lean_Parser_Tactic_match___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_match___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_match___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__9;
static const lean_string_object l_Lean_Parser_Tactic_match___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Parser_Tactic_match___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_match___closed__10_value;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__16;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__18;
static lean_once_cell_t l_Lean_Parser_Tactic_match___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match___closed__19;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 399, .m_capacity = 399, .m_length = 398, .m_data = "`match` performs case analysis on one or more expressions.\nSee [Induction and Recursion][tpil4].\nThe syntax for the `match` tactic is the same as term-mode `match`, except that\nthe match arms are tactics instead of expressions.\n```\nexample (n : Nat) : n = n := by\n  match n with\n  | 0 => rfl\n  | i+1 => simp\n```\n\n[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html\n"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_hole_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_matchRhs_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_syntheticHole_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_matchRhs_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_match___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__3_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_generalizingParam_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_motive_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_matchDiscr_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__7_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_match___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__8_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__10_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_formatter___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_match_formatter___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_match_formatter___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_formatter___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_match___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 240, 216, 203, 28, 130, 220)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 126, 137, 87, 84, 74, 117, 101)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_hole_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_match___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__3_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_generalizingParam_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_motive_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_matchDiscr_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__7_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_match___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__8_value;
static const lean_closure_object l_Lean_Parser_Tactic_match_parenthesizer___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_match___closed__10_value)} };
static const lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_match_parenthesizer___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_match_parenthesizer___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_match_parenthesizer___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_match___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 240, 216, 203, 28, 130, 220)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 207, 254, 115, 108, 126, 8, 190)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_introMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "introMatch"};
static const lean_object* l_Lean_Parser_Tactic_introMatch___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_introMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 42, 46, 143, 104, 41, 172, 166)}};
static const lean_object* l_Lean_Parser_Tactic_introMatch___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch___closed__2;
static const lean_string_object l_Lean_Parser_Tactic_introMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Parser_Tactic_introMatch___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_introMatch_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_introMatch_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 42, 46, 143, 104, 41, 172, 166)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 8, 173, 207, 249, 126, 136, 142)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_introMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 42, 46, 143, 104, 41, 172, 166)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 99, 187, 142, 166, 117, 137, 131)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "matchRhsTacticSeq"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 18, 144, 204, 99, 109, 250, 84)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchRhs"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 255, 189, 19, 172, 234, 14, 187)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = l_Lean_Parser_Tactic_tacticSeqIndentGt;
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___y_53_; lean_object* v___x_63_; 
v___x_47_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_48_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_49_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_);
v___x_50_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_51_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_63_ = l_Lean_Parser_registerAlias(v___x_47_, v___x_48_, v___x_49_, v___x_50_, v___x_51_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec_ref(v___x_63_);
v___x_64_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_65_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_47_, v___x_64_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec_ref(v___x_65_);
v___x_66_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_67_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_47_, v___x_66_);
v___y_53_ = v___x_67_;
goto v___jp_52_;
}
else
{
v___y_53_ = v___x_65_;
goto v___jp_52_;
}
}
else
{
v___y_53_ = v___x_63_;
goto v___jp_52_;
}
v___jp_52_:
{
if (lean_obj_tag(v___y_53_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref(v___y_53_);
v___x_54_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_55_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_56_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_);
v___x_57_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_58_ = l_Lean_Parser_registerAlias(v___x_54_, v___x_55_, v___x_56_, v___x_57_, v___x_51_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec_ref(v___x_58_);
v___x_59_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_60_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_54_, v___x_59_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec_ref(v___x_60_);
v___x_61_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_62_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_54_, v___x_61_);
return v___x_62_;
}
else
{
return v___x_60_;
}
}
else
{
return v___x_58_;
}
}
else
{
return v___y_53_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_();
return v_res_69_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__2(void){
_start:
{
uint8_t v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = 0;
v___x_77_ = 1;
v___x_78_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_79_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__0));
v___x_80_ = l_Lean_Parser_mkAntiquot(v___x_79_, v___x_78_, v___x_77_, v___x_76_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__4(void){
_start:
{
uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = 1;
v___x_83_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__3));
v___x_84_ = l_Lean_Parser_errorAtSavedPos(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__5(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__4, &l_Lean_Parser_Tactic_unknown___closed__4_once, _init_l_Lean_Parser_Tactic_unknown___closed__4);
v___x_86_ = l_Lean_Parser_ident;
v___x_87_ = l_Lean_Parser_andthen(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__6(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__5, &l_Lean_Parser_Tactic_unknown___closed__5_once, _init_l_Lean_Parser_Tactic_unknown___closed__5);
v___x_89_ = l_Lean_Parser_withPosition(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__7(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__6, &l_Lean_Parser_Tactic_unknown___closed__6_once, _init_l_Lean_Parser_Tactic_unknown___closed__6);
v___x_91_ = lean_unsigned_to_nat(1024u);
v___x_92_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_93_ = l_Lean_Parser_leadingNode(v___x_92_, v___x_91_, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__8(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__7, &l_Lean_Parser_Tactic_unknown___closed__7_once, _init_l_Lean_Parser_Tactic_unknown___closed__7);
v___x_95_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__2, &l_Lean_Parser_Tactic_unknown___closed__2_once, _init_l_Lean_Parser_Tactic_unknown___closed__2);
v___x_96_ = l_Lean_Parser_withAntiquot(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__9(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__8, &l_Lean_Parser_Tactic_unknown___closed__8_once, _init_l_Lean_Parser_Tactic_unknown___closed__8);
v___x_98_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_99_ = l_Lean_Parser_withCache(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__9, &l_Lean_Parser_Tactic_unknown___closed__9_once, _init_l_Lean_Parser_Tactic_unknown___closed__9);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1(){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_106_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_107_ = l_Lean_Parser_Tactic_unknown;
v___x_108_ = lean_unsigned_to_nat(1000u);
v___x_109_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_105_, v___x_106_, v___x_107_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___boxed(lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1();
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3(){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_139_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6));
v___x_140_ = l_Lean_addBuiltinDeclarationRanges(v___x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_formatter(lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_formatter___closed__0));
v___x_170_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_formatter___closed__5));
v___x_171_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_169_, v___x_170_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_formatter___boxed(lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Parser_Tactic_unknown_formatter(v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7(){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_186_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_187_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_188_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1));
v___x_189_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown_formatter___boxed), 5, 0);
v___x_190_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_186_, v___x_187_, v___x_188_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___boxed(lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7();
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer(lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0));
v___x_220_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5));
v___x_221_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_219_, v___x_220_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___boxed(lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Parser_Tactic_unknown_parenthesizer(v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11(){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_236_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_237_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_238_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1));
v___x_239_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown_parenthesizer___boxed), 5, 0);
v___x_240_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_236_, v___x_237_, v___x_238_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___boxed(lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11();
return v_res_242_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nestedTactic(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1(){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_252_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1));
v___x_253_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_254_ = lean_unsigned_to_nat(1000u);
v___x_255_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_251_, v___x_252_, v___x_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___boxed(lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1();
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3(){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1));
v___x_285_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6));
v___x_286_ = l_Lean_addBuiltinDeclarationRanges(v___x_284_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___boxed(lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3();
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter(lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter___boxed(lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Parser_Tactic_nestedTactic_formatter(v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(v_a_301_, v_a_302_, v_a_303_, v_a_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer___boxed(lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Parser_Tactic_nestedTactic_parenthesizer(v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_312_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__0(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_314_ = l_Lean_Parser_Term_syntheticHole;
v___x_315_ = l_Lean_Parser_orelse(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Parser_Tactic_matchRhs___closed__0, &l_Lean_Parser_Tactic_matchRhs___closed__0_once, _init_l_Lean_Parser_Tactic_matchRhs___closed__0);
v___x_317_ = l_Lean_Parser_Term_hole;
v___x_318_ = l_Lean_Parser_orelse(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lean_Parser_Tactic_matchRhs___closed__1, &l_Lean_Parser_Tactic_matchRhs___closed__1_once, _init_l_Lean_Parser_Tactic_matchRhs___closed__1);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = l_Lean_Parser_Tactic_matchRhs;
v___x_321_ = l_Lean_Parser_Term_matchAlts(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Lean_Parser_Tactic_matchAlts___closed__0, &l_Lean_Parser_Tactic_matchAlts___closed__0_once, _init_l_Lean_Parser_Tactic_matchAlts___closed__0);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__2(void){
_start:
{
uint8_t v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_329_ = 0;
v___x_330_ = 1;
v___x_331_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_332_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__0));
v___x_333_ = l_Lean_Parser_mkAntiquot(v___x_332_, v___x_331_, v___x_330_, v___x_329_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__4(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__3));
v___x_336_ = l_Lean_Parser_symbol(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__5(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Lean_Parser_Term_generalizingParam;
v___x_338_ = l_Lean_Parser_optional(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__6(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = l_Lean_Parser_Term_motive;
v___x_340_ = l_Lean_Parser_optional(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__8(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__7));
v___x_343_ = l_Lean_Parser_symbol(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__9(void){
_start:
{
uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_344_ = 0;
v___x_345_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__8, &l_Lean_Parser_Tactic_match___closed__8_once, _init_l_Lean_Parser_Tactic_match___closed__8);
v___x_346_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__7));
v___x_347_ = l_Lean_Parser_Term_matchDiscr;
v___x_348_ = l_Lean_Parser_sepBy1(v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__11(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__10));
v___x_351_ = l_Lean_Parser_symbol(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__12(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = l_Lean_Parser_Tactic_matchAlts;
v___x_353_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__11, &l_Lean_Parser_Tactic_match___closed__11_once, _init_l_Lean_Parser_Tactic_match___closed__11);
v___x_354_ = l_Lean_Parser_andthen(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__13(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__12, &l_Lean_Parser_Tactic_match___closed__12_once, _init_l_Lean_Parser_Tactic_match___closed__12);
v___x_356_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__9, &l_Lean_Parser_Tactic_match___closed__9_once, _init_l_Lean_Parser_Tactic_match___closed__9);
v___x_357_ = l_Lean_Parser_andthen(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__14(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__13, &l_Lean_Parser_Tactic_match___closed__13_once, _init_l_Lean_Parser_Tactic_match___closed__13);
v___x_359_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__6, &l_Lean_Parser_Tactic_match___closed__6_once, _init_l_Lean_Parser_Tactic_match___closed__6);
v___x_360_ = l_Lean_Parser_andthen(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__15(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__14, &l_Lean_Parser_Tactic_match___closed__14_once, _init_l_Lean_Parser_Tactic_match___closed__14);
v___x_362_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__5, &l_Lean_Parser_Tactic_match___closed__5_once, _init_l_Lean_Parser_Tactic_match___closed__5);
v___x_363_ = l_Lean_Parser_andthen(v___x_362_, v___x_361_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__16(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__15, &l_Lean_Parser_Tactic_match___closed__15_once, _init_l_Lean_Parser_Tactic_match___closed__15);
v___x_365_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__4, &l_Lean_Parser_Tactic_match___closed__4_once, _init_l_Lean_Parser_Tactic_match___closed__4);
v___x_366_ = l_Lean_Parser_andthen(v___x_365_, v___x_364_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__17(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__16, &l_Lean_Parser_Tactic_match___closed__16_once, _init_l_Lean_Parser_Tactic_match___closed__16);
v___x_368_ = l_Lean_Parser_leadPrec;
v___x_369_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_370_ = l_Lean_Parser_leadingNode(v___x_369_, v___x_368_, v___x_367_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__18(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__17, &l_Lean_Parser_Tactic_match___closed__17_once, _init_l_Lean_Parser_Tactic_match___closed__17);
v___x_372_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__2, &l_Lean_Parser_Tactic_match___closed__2_once, _init_l_Lean_Parser_Tactic_match___closed__2);
v___x_373_ = l_Lean_Parser_withAntiquot(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__19(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__18, &l_Lean_Parser_Tactic_match___closed__18_once, _init_l_Lean_Parser_Tactic_match___closed__18);
v___x_375_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_376_ = l_Lean_Parser_withCache(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__19, &l_Lean_Parser_Tactic_match___closed__19_once, _init_l_Lean_Parser_Tactic_match___closed__19);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1(){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_380_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_381_ = l_Lean_Parser_Tactic_match;
v___x_382_ = lean_unsigned_to_nat(1000u);
v___x_383_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_379_, v___x_380_, v___x_381_, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1___boxed(lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1();
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3(){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_389_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0));
v___x_390_ = l_Lean_addBuiltinDocString(v___x_388_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___boxed(lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3();
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_420_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6));
v___x_421_ = l_Lean_addBuiltinDeclarationRanges(v___x_419_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___boxed(lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5();
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_formatter(lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_formatter___closed__0));
v___x_435_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_formatter___closed__2));
v___x_436_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_434_, v___x_435_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___boxed(lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Parser_Tactic_matchRhs_formatter(v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_formatter(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_formatter___boxed), 5, 0);
v___x_449_ = l_Lean_Parser_Term_matchAlts_formatter(v___x_448_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_formatter___boxed(lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Parser_Tactic_matchAlts_formatter(v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_455_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__10(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_formatter___boxed), 5, 0);
v___x_483_ = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter___boxed), 6, 1);
lean_closure_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__11(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__10, &l_Lean_Parser_Tactic_match_formatter___closed__10_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__10);
v___x_485_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__9));
v___x_486_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_486_, 0, v___x_485_);
lean_closure_set(v___x_486_, 1, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__12(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__11, &l_Lean_Parser_Tactic_match_formatter___closed__11_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__11);
v___x_488_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__8));
v___x_489_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_489_, 0, v___x_488_);
lean_closure_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__13(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__12, &l_Lean_Parser_Tactic_match_formatter___closed__12_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__12);
v___x_491_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__5));
v___x_492_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_492_, 0, v___x_491_);
lean_closure_set(v___x_492_, 1, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__14(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__13, &l_Lean_Parser_Tactic_match_formatter___closed__13_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__13);
v___x_494_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__3));
v___x_495_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_495_, 0, v___x_494_);
lean_closure_set(v___x_495_, 1, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__15(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__14, &l_Lean_Parser_Tactic_match_formatter___closed__14_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__14);
v___x_497_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__1));
v___x_498_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_498_, 0, v___x_497_);
lean_closure_set(v___x_498_, 1, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__16(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__15, &l_Lean_Parser_Tactic_match_formatter___closed__15_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__15);
v___x_500_ = l_Lean_Parser_leadPrec;
v___x_501_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_502_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_502_, 0, v___x_501_);
lean_closure_set(v___x_502_, 1, v___x_500_);
lean_closure_set(v___x_502_, 2, v___x_499_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_formatter(lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__0));
v___x_509_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__16, &l_Lean_Parser_Tactic_match_formatter___closed__16_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__16);
v___x_510_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_508_, v___x_509_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_formatter___boxed(lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Parser_Tactic_match_formatter(v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13(){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_524_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_525_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_526_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0));
v___x_527_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match_formatter___boxed), 5, 0);
v___x_528_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_524_, v___x_525_, v___x_526_, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___boxed(lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13();
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer(lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0));
v___x_542_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2));
v___x_543_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_541_, v___x_542_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed(lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Parser_Tactic_matchRhs_parenthesizer(v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer(lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed), 5, 0);
v___x_556_ = l_Lean_Parser_Term_matchAlts_parenthesizer(v___x_555_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed(lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Parser_Tactic_matchAlts_parenthesizer(v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed), 5, 0);
v___x_590_ = lean_alloc_closure((void*)(l_Lean_Parser_ppDedent_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__10, &l_Lean_Parser_Tactic_match_parenthesizer___closed__10_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__10);
v___x_592_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__9));
v___x_593_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_593_, 0, v___x_592_);
lean_closure_set(v___x_593_, 1, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__11, &l_Lean_Parser_Tactic_match_parenthesizer___closed__11_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__11);
v___x_595_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__8));
v___x_596_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_596_, 0, v___x_595_);
lean_closure_set(v___x_596_, 1, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__12, &l_Lean_Parser_Tactic_match_parenthesizer___closed__12_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__12);
v___x_598_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__5));
v___x_599_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_599_, 0, v___x_598_);
lean_closure_set(v___x_599_, 1, v___x_597_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__14(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__13, &l_Lean_Parser_Tactic_match_parenthesizer___closed__13_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__13);
v___x_601_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__3));
v___x_602_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_602_, 0, v___x_601_);
lean_closure_set(v___x_602_, 1, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__15(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__14, &l_Lean_Parser_Tactic_match_parenthesizer___closed__14_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__14);
v___x_604_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__1));
v___x_605_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_605_, 0, v___x_604_);
lean_closure_set(v___x_605_, 1, v___x_603_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__16(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_606_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__15, &l_Lean_Parser_Tactic_match_parenthesizer___closed__15_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__15);
v___x_607_ = l_Lean_Parser_leadPrec;
v___x_608_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_609_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_609_, 0, v___x_608_);
lean_closure_set(v___x_609_, 1, v___x_607_);
lean_closure_set(v___x_609_, 2, v___x_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_parenthesizer(lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__0));
v___x_616_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__16, &l_Lean_Parser_Tactic_match_parenthesizer___closed__16_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__16);
v___x_617_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_615_, v___x_616_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_parenthesizer___boxed(lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Parser_Tactic_match_parenthesizer(v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21(){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_632_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_633_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0));
v___x_634_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match_parenthesizer___boxed), 5, 0);
v___x_635_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_631_, v___x_632_, v___x_633_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___boxed(lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21();
return v_res_637_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__2(void){
_start:
{
uint8_t v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_644_ = 0;
v___x_645_ = 1;
v___x_646_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_647_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__0));
v___x_648_ = l_Lean_Parser_mkAntiquot(v___x_647_, v___x_646_, v___x_645_, v___x_644_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__4(void){
_start:
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = 0;
v___x_651_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__3));
v___x_652_ = l_Lean_Parser_nonReservedSymbol(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__5(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = l_Lean_Parser_Tactic_matchAlts;
v___x_654_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__4, &l_Lean_Parser_Tactic_introMatch___closed__4_once, _init_l_Lean_Parser_Tactic_introMatch___closed__4);
v___x_655_ = l_Lean_Parser_andthen(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__6(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__5, &l_Lean_Parser_Tactic_introMatch___closed__5_once, _init_l_Lean_Parser_Tactic_introMatch___closed__5);
v___x_657_ = lean_unsigned_to_nat(1024u);
v___x_658_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_659_ = l_Lean_Parser_leadingNode(v___x_658_, v___x_657_, v___x_656_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__7(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__6, &l_Lean_Parser_Tactic_introMatch___closed__6_once, _init_l_Lean_Parser_Tactic_introMatch___closed__6);
v___x_661_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__2, &l_Lean_Parser_Tactic_introMatch___closed__2_once, _init_l_Lean_Parser_Tactic_introMatch___closed__2);
v___x_662_ = l_Lean_Parser_withAntiquot(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__8(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__7, &l_Lean_Parser_Tactic_introMatch___closed__7_once, _init_l_Lean_Parser_Tactic_introMatch___closed__7);
v___x_664_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_665_ = l_Lean_Parser_withCache(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch(void){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__8, &l_Lean_Parser_Tactic_introMatch___closed__8_once, _init_l_Lean_Parser_Tactic_introMatch___closed__8);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1(){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_669_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_670_ = l_Lean_Parser_Tactic_introMatch;
v___x_671_ = lean_unsigned_to_nat(1000u);
v___x_672_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_668_, v___x_669_, v___x_670_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1___boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1();
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3(){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_702_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6));
v___x_703_ = l_Lean_addBuiltinDeclarationRanges(v___x_701_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___boxed(lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3();
return v_res_705_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_formatter___boxed), 5, 0);
v___x_718_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_formatter___closed__1));
v___x_719_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_719_, 0, v___x_718_);
lean_closure_set(v___x_719_, 1, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_formatter___closed__2, &l_Lean_Parser_Tactic_introMatch_formatter___closed__2_once, _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2);
v___x_721_ = lean_unsigned_to_nat(1024u);
v___x_722_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_723_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_723_, 0, v___x_722_);
lean_closure_set(v___x_723_, 1, v___x_721_);
lean_closure_set(v___x_723_, 2, v___x_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_formatter(lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_formatter___closed__0));
v___x_730_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_formatter___closed__3, &l_Lean_Parser_Tactic_introMatch_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3);
v___x_731_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_729_, v___x_730_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_formatter___boxed(lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Parser_Tactic_introMatch_formatter(v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7(){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_745_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_746_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_747_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0));
v___x_748_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch_formatter___boxed), 5, 0);
v___x_749_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_745_, v___x_746_, v___x_747_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___boxed(lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7();
return v_res_751_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed), 5, 0);
v___x_764_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1));
v___x_765_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_765_, 0, v___x_764_);
lean_closure_set(v___x_765_, 1, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2, &l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2_once, _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2);
v___x_767_ = lean_unsigned_to_nat(1024u);
v___x_768_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_769_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_769_, 0, v___x_768_);
lean_closure_set(v___x_769_, 1, v___x_767_);
lean_closure_set(v___x_769_, 2, v___x_766_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0));
v___x_776_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3, &l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3_once, _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3);
v___x_777_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_775_, v___x_776_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed(lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Parser_Tactic_introMatch_parenthesizer(v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11(){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_791_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_792_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_793_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0));
v___x_794_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed), 5, 0);
v___x_795_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_791_, v___x_792_, v___x_793_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___boxed(lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11();
return v_res_797_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = l_Lean_Parser_Tactic_matchRhs;
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_formatter___boxed), 5, 0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed), 5, 0);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_));
v___x_817_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_));
v___x_818_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
v___x_819_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_));
v___x_820_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_821_ = l_Lean_Parser_registerAlias(v___x_816_, v___x_817_, v___x_818_, v___x_819_, v___x_820_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref(v___x_821_);
v___x_822_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
v___x_823_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_816_, v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v___x_823_);
v___x_824_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
v___x_825_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_816_, v___x_824_);
return v___x_825_;
}
else
{
return v___x_823_;
}
}
else
{
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2____boxed(lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_();
return v_res_827_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_unknown = _init_l_Lean_Parser_Tactic_unknown();
lean_mark_persistent(l_Lean_Parser_Tactic_unknown);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_nestedTactic = _init_l_Lean_Parser_Tactic_nestedTactic();
lean_mark_persistent(l_Lean_Parser_Tactic_nestedTactic);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_matchRhs = _init_l_Lean_Parser_Tactic_matchRhs();
lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs);
l_Lean_Parser_Tactic_matchAlts = _init_l_Lean_Parser_Tactic_matchAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_matchAlts);
l_Lean_Parser_Tactic_match = _init_l_Lean_Parser_Tactic_match();
lean_mark_persistent(l_Lean_Parser_Tactic_match);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_introMatch = _init_l_Lean_Parser_Tactic_introMatch();
lean_mark_persistent(l_Lean_Parser_Tactic_introMatch);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Tactic(builtin);
}
#ifdef __cplusplus
}
#endif
