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
lean_object* l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeq_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticSeqIndentGt"};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 96, 154, 40, 0, 37, 199, 17)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 234, 202, 179, 65, 11, 242, 216)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 398, .m_capacity = 398, .m_length = 397, .m_data = "`match` performs case analysis on one or more expressions.\nSee [Induction and Recursion][tpil4].\nThe syntax for the `match` tactic is the same as term-mode `match`, except that\nthe match arms are tactics instead of expressions.\n```\nexample (n : Nat) : n = n := by\n  match n with\n  | 0 => rfl\n  | i+1 => simp\n```\n\n[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html"};
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
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)} };
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
static const lean_closure_object l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value),((lean_object*)&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value)} };
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
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = l_Lean_Parser_Tactic_tacticSeqIndentGt;
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_47_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_48_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_49_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_);
v___x_50_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_51_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_52_ = l_Lean_Parser_registerAlias(v___x_47_, v___x_48_, v___x_49_, v___x_50_, v___x_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec_ref_known(v___x_52_, 1);
v___x_53_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_54_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_47_, v___x_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec_ref_known(v___x_54_, 1);
v___x_55_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_56_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_47_, v___x_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec_ref_known(v___x_56_, 1);
v___x_57_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_58_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_59_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_);
v___x_60_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_61_ = l_Lean_Parser_registerAlias(v___x_57_, v___x_58_, v___x_59_, v___x_60_, v___x_51_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec_ref_known(v___x_61_, 1);
v___x_62_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_63_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_57_, v___x_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec_ref_known(v___x_63_, 1);
v___x_64_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_65_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_57_, v___x_64_);
return v___x_65_;
}
else
{
return v___x_63_;
}
}
else
{
return v___x_61_;
}
}
else
{
return v___x_56_;
}
}
else
{
return v___x_54_;
}
}
else
{
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_();
return v_res_67_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__2(void){
_start:
{
uint8_t v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = 0;
v___x_75_ = 1;
v___x_76_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_77_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__0));
v___x_78_ = l_Lean_Parser_mkAntiquot(v___x_77_, v___x_76_, v___x_75_, v___x_74_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__4(void){
_start:
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = 1;
v___x_81_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__3));
v___x_82_ = l_Lean_Parser_errorAtSavedPos(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__5(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__4, &l_Lean_Parser_Tactic_unknown___closed__4_once, _init_l_Lean_Parser_Tactic_unknown___closed__4);
v___x_84_ = l_Lean_Parser_ident;
v___x_85_ = l_Lean_Parser_andthen(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__6(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__5, &l_Lean_Parser_Tactic_unknown___closed__5_once, _init_l_Lean_Parser_Tactic_unknown___closed__5);
v___x_87_ = l_Lean_Parser_withPosition(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__7(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__6, &l_Lean_Parser_Tactic_unknown___closed__6_once, _init_l_Lean_Parser_Tactic_unknown___closed__6);
v___x_89_ = lean_unsigned_to_nat(1024u);
v___x_90_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_91_ = l_Lean_Parser_leadingNode(v___x_90_, v___x_89_, v___x_88_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__8(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__7, &l_Lean_Parser_Tactic_unknown___closed__7_once, _init_l_Lean_Parser_Tactic_unknown___closed__7);
v___x_93_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__2, &l_Lean_Parser_Tactic_unknown___closed__2_once, _init_l_Lean_Parser_Tactic_unknown___closed__2);
v___x_94_ = l_Lean_Parser_withAntiquot(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown___closed__9(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__8, &l_Lean_Parser_Tactic_unknown___closed__8_once, _init_l_Lean_Parser_Tactic_unknown___closed__8);
v___x_96_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_97_ = l_Lean_Parser_withCache(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_unknown(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Parser_Tactic_unknown___closed__9, &l_Lean_Parser_Tactic_unknown___closed__9_once, _init_l_Lean_Parser_Tactic_unknown___closed__9);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1(){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_103_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_104_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_105_ = l_Lean_Parser_Tactic_unknown;
v___x_106_ = lean_unsigned_to_nat(1000u);
v___x_107_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_103_, v___x_104_, v___x_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___boxed(lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1();
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3(){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_137_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6));
v___x_138_ = l_Lean_addBuiltinDeclarationRanges(v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_formatter(lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_formatter___closed__0));
v___x_168_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_formatter___closed__5));
v___x_169_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_167_, v___x_168_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_formatter___boxed(lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Parser_Tactic_unknown_formatter(v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7(){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_184_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_185_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_186_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1));
v___x_187_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown_formatter___boxed), 5, 0);
v___x_188_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_184_, v___x_185_, v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer(lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0));
v___x_218_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5));
v___x_219_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_217_, v___x_218_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_unknown_parenthesizer___boxed(lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Parser_Tactic_unknown_parenthesizer(v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11(){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_234_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_235_ = ((lean_object*)(l_Lean_Parser_Tactic_unknown___closed__1));
v___x_236_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1));
v___x_237_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_unknown_parenthesizer___boxed), 5, 0);
v___x_238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_234_, v___x_235_, v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11();
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_nestedTactic(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1(){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_250_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1));
v___x_251_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
v___x_252_ = lean_unsigned_to_nat(1000u);
v___x_253_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_249_, v___x_250_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1();
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1));
v___x_283_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6));
v___x_284_ = l_Lean_addBuiltinDeclarationRanges(v___x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___boxed(lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3();
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter(lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_formatter___boxed(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Parser_Tactic_nestedTactic_formatter(v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer(lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(v_a_299_, v_a_300_, v_a_301_, v_a_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_nestedTactic_parenthesizer___boxed(lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Parser_Tactic_nestedTactic_parenthesizer(v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_310_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l_Lean_Parser_Tactic_tacticSeq;
v___x_312_ = l_Lean_Parser_Term_syntheticHole;
v___x_313_ = l_Lean_Parser_orelse(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_Lean_Parser_Tactic_matchRhs___closed__0, &l_Lean_Parser_Tactic_matchRhs___closed__0_once, _init_l_Lean_Parser_Tactic_matchRhs___closed__0);
v___x_315_ = l_Lean_Parser_Term_hole;
v___x_316_ = l_Lean_Parser_orelse(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchRhs(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_Parser_Tactic_matchRhs___closed__1, &l_Lean_Parser_Tactic_matchRhs___closed__1_once, _init_l_Lean_Parser_Tactic_matchRhs___closed__1);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts___closed__0(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = l_Lean_Parser_Tactic_matchRhs;
v___x_319_ = l_Lean_Parser_Term_matchAlts(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_matchAlts(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Lean_Parser_Tactic_matchAlts___closed__0, &l_Lean_Parser_Tactic_matchAlts___closed__0_once, _init_l_Lean_Parser_Tactic_matchAlts___closed__0);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__2(void){
_start:
{
uint8_t v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = 0;
v___x_328_ = 1;
v___x_329_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_330_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__0));
v___x_331_ = l_Lean_Parser_mkAntiquot(v___x_330_, v___x_329_, v___x_328_, v___x_327_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__4(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__3));
v___x_334_ = l_Lean_Parser_symbol(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__5(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Lean_Parser_Term_generalizingParam;
v___x_336_ = l_Lean_Parser_optional(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__6(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Lean_Parser_Term_motive;
v___x_338_ = l_Lean_Parser_optional(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__8(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__7));
v___x_341_ = l_Lean_Parser_symbol(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__9(void){
_start:
{
uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_342_ = 0;
v___x_343_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__8, &l_Lean_Parser_Tactic_match___closed__8_once, _init_l_Lean_Parser_Tactic_match___closed__8);
v___x_344_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__7));
v___x_345_ = l_Lean_Parser_Term_matchDiscr;
v___x_346_ = l_Lean_Parser_sepBy1(v___x_345_, v___x_344_, v___x_343_, v___x_342_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__11(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__10));
v___x_349_ = l_Lean_Parser_symbol(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__12(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = l_Lean_Parser_Tactic_matchAlts;
v___x_351_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__11, &l_Lean_Parser_Tactic_match___closed__11_once, _init_l_Lean_Parser_Tactic_match___closed__11);
v___x_352_ = l_Lean_Parser_andthen(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__13(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__12, &l_Lean_Parser_Tactic_match___closed__12_once, _init_l_Lean_Parser_Tactic_match___closed__12);
v___x_354_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__9, &l_Lean_Parser_Tactic_match___closed__9_once, _init_l_Lean_Parser_Tactic_match___closed__9);
v___x_355_ = l_Lean_Parser_andthen(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__14(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__13, &l_Lean_Parser_Tactic_match___closed__13_once, _init_l_Lean_Parser_Tactic_match___closed__13);
v___x_357_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__6, &l_Lean_Parser_Tactic_match___closed__6_once, _init_l_Lean_Parser_Tactic_match___closed__6);
v___x_358_ = l_Lean_Parser_andthen(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__15(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__14, &l_Lean_Parser_Tactic_match___closed__14_once, _init_l_Lean_Parser_Tactic_match___closed__14);
v___x_360_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__5, &l_Lean_Parser_Tactic_match___closed__5_once, _init_l_Lean_Parser_Tactic_match___closed__5);
v___x_361_ = l_Lean_Parser_andthen(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__16(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__15, &l_Lean_Parser_Tactic_match___closed__15_once, _init_l_Lean_Parser_Tactic_match___closed__15);
v___x_363_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__4, &l_Lean_Parser_Tactic_match___closed__4_once, _init_l_Lean_Parser_Tactic_match___closed__4);
v___x_364_ = l_Lean_Parser_andthen(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__17(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__16, &l_Lean_Parser_Tactic_match___closed__16_once, _init_l_Lean_Parser_Tactic_match___closed__16);
v___x_366_ = l_Lean_Parser_leadPrec;
v___x_367_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_368_ = l_Lean_Parser_leadingNode(v___x_367_, v___x_366_, v___x_365_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__18(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__17, &l_Lean_Parser_Tactic_match___closed__17_once, _init_l_Lean_Parser_Tactic_match___closed__17);
v___x_370_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__2, &l_Lean_Parser_Tactic_match___closed__2_once, _init_l_Lean_Parser_Tactic_match___closed__2);
v___x_371_ = l_Lean_Parser_withAntiquot(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match___closed__19(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__18, &l_Lean_Parser_Tactic_match___closed__18_once, _init_l_Lean_Parser_Tactic_match___closed__18);
v___x_373_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_374_ = l_Lean_Parser_withCache(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Lean_Parser_Tactic_match___closed__19, &l_Lean_Parser_Tactic_match___closed__19_once, _init_l_Lean_Parser_Tactic_match___closed__19);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1(){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_378_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_379_ = l_Lean_Parser_Tactic_match;
v___x_380_ = lean_unsigned_to_nat(1000u);
v___x_381_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_377_, v___x_378_, v___x_379_, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1___boxed(lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1();
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3(){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_387_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0));
v___x_388_ = l_Lean_addBuiltinDocString(v___x_386_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___boxed(lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5(){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_418_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6));
v___x_419_ = l_Lean_addBuiltinDeclarationRanges(v___x_417_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___boxed(lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5();
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_formatter(lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_formatter___closed__0));
v___x_433_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_formatter___closed__2));
v___x_434_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_432_, v___x_433_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_formatter___boxed(lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Parser_Tactic_matchRhs_formatter(v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_formatter(lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_formatter___boxed), 5, 0);
v___x_447_ = l_Lean_Parser_Term_matchAlts_formatter(v___x_446_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_formatter___boxed(lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Parser_Tactic_matchAlts_formatter(v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_453_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__10(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_formatter___boxed), 5, 0);
v___x_481_ = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter___boxed), 6, 1);
lean_closure_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__11(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__10, &l_Lean_Parser_Tactic_match_formatter___closed__10_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__10);
v___x_483_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__9));
v___x_484_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_484_, 0, v___x_483_);
lean_closure_set(v___x_484_, 1, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__12(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__11, &l_Lean_Parser_Tactic_match_formatter___closed__11_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__11);
v___x_486_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__8));
v___x_487_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_487_, 0, v___x_486_);
lean_closure_set(v___x_487_, 1, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__13(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__12, &l_Lean_Parser_Tactic_match_formatter___closed__12_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__12);
v___x_489_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__5));
v___x_490_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_490_, 0, v___x_489_);
lean_closure_set(v___x_490_, 1, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__14(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__13, &l_Lean_Parser_Tactic_match_formatter___closed__13_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__13);
v___x_492_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__3));
v___x_493_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_493_, 0, v___x_492_);
lean_closure_set(v___x_493_, 1, v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__15(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__14, &l_Lean_Parser_Tactic_match_formatter___closed__14_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__14);
v___x_495_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__1));
v___x_496_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_496_, 0, v___x_495_);
lean_closure_set(v___x_496_, 1, v___x_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_formatter___closed__16(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__15, &l_Lean_Parser_Tactic_match_formatter___closed__15_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__15);
v___x_498_ = l_Lean_Parser_leadPrec;
v___x_499_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_500_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_500_, 0, v___x_499_);
lean_closure_set(v___x_500_, 1, v___x_498_);
lean_closure_set(v___x_500_, 2, v___x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_formatter(lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((lean_object*)(l_Lean_Parser_Tactic_match_formatter___closed__0));
v___x_507_ = lean_obj_once(&l_Lean_Parser_Tactic_match_formatter___closed__16, &l_Lean_Parser_Tactic_match_formatter___closed__16_once, _init_l_Lean_Parser_Tactic_match_formatter___closed__16);
v___x_508_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_506_, v___x_507_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_formatter___boxed(lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Parser_Tactic_match_formatter(v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13(){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_523_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_524_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0));
v___x_525_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match_formatter___boxed), 5, 0);
v___x_526_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_522_, v___x_523_, v___x_524_, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___boxed(lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13();
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer(lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0));
v___x_540_ = ((lean_object*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2));
v___x_541_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_539_, v___x_540_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Parser_Tactic_matchRhs_parenthesizer(v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer(lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed), 5, 0);
v___x_554_ = l_Lean_Parser_Term_matchAlts_parenthesizer(v___x_553_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed(lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Parser_Tactic_matchAlts_parenthesizer(v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_560_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed), 5, 0);
v___x_588_ = lean_alloc_closure((void*)(l_Lean_Parser_ppDedent_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__10, &l_Lean_Parser_Tactic_match_parenthesizer___closed__10_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__10);
v___x_590_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__9));
v___x_591_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_591_, 0, v___x_590_);
lean_closure_set(v___x_591_, 1, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__11, &l_Lean_Parser_Tactic_match_parenthesizer___closed__11_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__11);
v___x_593_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__8));
v___x_594_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_594_, 0, v___x_593_);
lean_closure_set(v___x_594_, 1, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__12, &l_Lean_Parser_Tactic_match_parenthesizer___closed__12_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__12);
v___x_596_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__5));
v___x_597_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_597_, 0, v___x_596_);
lean_closure_set(v___x_597_, 1, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__14(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__13, &l_Lean_Parser_Tactic_match_parenthesizer___closed__13_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__13);
v___x_599_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__3));
v___x_600_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_600_, 0, v___x_599_);
lean_closure_set(v___x_600_, 1, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__15(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__14, &l_Lean_Parser_Tactic_match_parenthesizer___closed__14_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__14);
v___x_602_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__1));
v___x_603_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_603_, 0, v___x_602_);
lean_closure_set(v___x_603_, 1, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__16(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__15, &l_Lean_Parser_Tactic_match_parenthesizer___closed__15_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__15);
v___x_605_ = l_Lean_Parser_leadPrec;
v___x_606_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_607_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_607_, 0, v___x_606_);
lean_closure_set(v___x_607_, 1, v___x_605_);
lean_closure_set(v___x_607_, 2, v___x_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_parenthesizer(lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((lean_object*)(l_Lean_Parser_Tactic_match_parenthesizer___closed__0));
v___x_614_ = lean_obj_once(&l_Lean_Parser_Tactic_match_parenthesizer___closed__16, &l_Lean_Parser_Tactic_match_parenthesizer___closed__16_once, _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__16);
v___x_615_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_613_, v___x_614_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_match_parenthesizer___boxed(lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Parser_Tactic_match_parenthesizer(v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21(){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_629_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_630_ = ((lean_object*)(l_Lean_Parser_Tactic_match___closed__1));
v___x_631_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0));
v___x_632_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_match_parenthesizer___boxed), 5, 0);
v___x_633_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_629_, v___x_630_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___boxed(lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21();
return v_res_635_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__2(void){
_start:
{
uint8_t v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_642_ = 0;
v___x_643_ = 1;
v___x_644_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_645_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__0));
v___x_646_ = l_Lean_Parser_mkAntiquot(v___x_645_, v___x_644_, v___x_643_, v___x_642_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__4(void){
_start:
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = 0;
v___x_649_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__3));
v___x_650_ = l_Lean_Parser_nonReservedSymbol(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__5(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = l_Lean_Parser_Tactic_matchAlts;
v___x_652_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__4, &l_Lean_Parser_Tactic_introMatch___closed__4_once, _init_l_Lean_Parser_Tactic_introMatch___closed__4);
v___x_653_ = l_Lean_Parser_andthen(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__6(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__5, &l_Lean_Parser_Tactic_introMatch___closed__5_once, _init_l_Lean_Parser_Tactic_introMatch___closed__5);
v___x_655_ = lean_unsigned_to_nat(1024u);
v___x_656_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_657_ = l_Lean_Parser_leadingNode(v___x_656_, v___x_655_, v___x_654_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__7(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__6, &l_Lean_Parser_Tactic_introMatch___closed__6_once, _init_l_Lean_Parser_Tactic_introMatch___closed__6);
v___x_659_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__2, &l_Lean_Parser_Tactic_introMatch___closed__2_once, _init_l_Lean_Parser_Tactic_introMatch___closed__2);
v___x_660_ = l_Lean_Parser_withAntiquot(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch___closed__8(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__7, &l_Lean_Parser_Tactic_introMatch___closed__7_once, _init_l_Lean_Parser_Tactic_introMatch___closed__7);
v___x_662_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_663_ = l_Lean_Parser_withCache(v___x_662_, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch(void){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch___closed__8, &l_Lean_Parser_Tactic_introMatch___closed__8_once, _init_l_Lean_Parser_Tactic_introMatch___closed__8);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1(){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1));
v___x_667_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_668_ = l_Lean_Parser_Tactic_introMatch;
v___x_669_ = lean_unsigned_to_nat(1000u);
v___x_670_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_666_, v___x_667_, v___x_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1___boxed(lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1();
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3(){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_700_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6));
v___x_701_ = l_Lean_addBuiltinDeclarationRanges(v___x_699_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___boxed(lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3();
return v_res_703_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_formatter___boxed), 5, 0);
v___x_716_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_formatter___closed__1));
v___x_717_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_717_, 0, v___x_716_);
lean_closure_set(v___x_717_, 1, v___x_715_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_formatter___closed__2, &l_Lean_Parser_Tactic_introMatch_formatter___closed__2_once, _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2);
v___x_719_ = lean_unsigned_to_nat(1024u);
v___x_720_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_721_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_721_, 0, v___x_720_);
lean_closure_set(v___x_721_, 1, v___x_719_);
lean_closure_set(v___x_721_, 2, v___x_718_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_formatter(lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_formatter___closed__0));
v___x_728_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_formatter___closed__3, &l_Lean_Parser_Tactic_introMatch_formatter___closed__3_once, _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3);
v___x_729_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_727_, v___x_728_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_formatter___boxed(lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Parser_Tactic_introMatch_formatter(v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7(){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_744_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_745_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0));
v___x_746_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch_formatter___boxed), 5, 0);
v___x_747_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_743_, v___x_744_, v___x_745_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___boxed(lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7();
return v_res_749_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed), 5, 0);
v___x_762_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1));
v___x_763_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_763_, 0, v___x_762_);
lean_closure_set(v___x_763_, 1, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2, &l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2_once, _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2);
v___x_765_ = lean_unsigned_to_nat(1024u);
v___x_766_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_767_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_767_, 0, v___x_766_);
lean_closure_set(v___x_767_, 1, v___x_765_);
lean_closure_set(v___x_767_, 2, v___x_764_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer(lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0));
v___x_774_ = lean_obj_once(&l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3, &l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3_once, _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3);
v___x_775_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_773_, v___x_774_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed(lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Parser_Tactic_introMatch_parenthesizer(v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11(){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_789_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_790_ = ((lean_object*)(l_Lean_Parser_Tactic_introMatch___closed__1));
v___x_791_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0));
v___x_792_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed), 5, 0);
v___x_793_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_789_, v___x_790_, v___x_791_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___boxed(lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11();
return v_res_795_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = l_Lean_Parser_Tactic_matchRhs;
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_formatter___boxed), 5, 0);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed), 5, 0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_814_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_));
v___x_815_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_));
v___x_816_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
v___x_817_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_));
v___x_818_ = ((lean_object*)(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_));
v___x_819_ = l_Lean_Parser_registerAlias(v___x_814_, v___x_815_, v___x_816_, v___x_817_, v___x_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref_known(v___x_819_, 1);
v___x_820_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
v___x_821_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_814_, v___x_820_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref_known(v___x_821_, 1);
v___x_822_ = lean_obj_once(&l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
v___x_823_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_814_, v___x_822_);
return v___x_823_;
}
else
{
return v___x_821_;
}
}
else
{
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2____boxed(lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_();
return v_res_825_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
