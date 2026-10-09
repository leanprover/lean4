// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Parser
// Imports: public import Lean.Parser.Command
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
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_darrow;
extern lean_object* l_Lean_Parser_Term_attrKind;
lean_object* l_Lean_Parser_termParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_darrow_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_attrKind_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_darrow_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_attrKind_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* l_Lean_Parser_many_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "GrindCnstr"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__4 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 127, 91, 31, 152, 192, 239, 0)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__6;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "is_value "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__7 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__8;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__9 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__12;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__13;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__14;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__15;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isValue___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isValue___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isStrictValue"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 167, 118, 192, 170, 54, 174, 22)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "is_strict_value "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notValue"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 180, 19, 60, 251, 16, 248, 4)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_value "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notValue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notValue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notValue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notValue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notValue___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "notStrictValue"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 251, 19, 154, 122, 46, 102, 83)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not_strict_value "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isGround"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 99, 47, 57, 220, 158, 80, 177)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isGround___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "is_ground "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isGround___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isGround___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isGround___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isGround___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_isGround___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_isGround___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sizeLt"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 251, 30, 194, 200, 196, 155, 146)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "size "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " < "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depthLt"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 13, 145, 164, 157, 20, 85, 11)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "depth "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "genLt"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 6, 178, 35, 133, 139, 189, 47)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_genLt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gen"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_genLt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_genLt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_genLt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_genLt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_genLt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_genLt___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxInsts"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 108, 68, 184, 240, 212, 209, 21)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "max_insts"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "guard"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 187, 126, 138, 230, 109, 238, 75)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "guard "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__4;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_guard___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__12;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 211, 65, 46, 115, 168, 222, 235)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_check___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "check "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notDefEq"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 71, 120, 134, 181, 74, 206, 169)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =/= "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "defEq"};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 16, 176, 15, 194, 80, 158, 173)}};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__2;
static const lean_string_object l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__0;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__1;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__2;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr;
static const lean_string_object l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grindPatternCnstrs"};
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__0 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 242, 154, 125, 67, 48, 229, 39)}};
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__1 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__2;
static const lean_string_object l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "where "};
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__3 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs;
static const lean_string_object l_Lean_Parser_Command_grindPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindPattern"};
static const lean_object* l_Lean_Parser_Command_grindPattern___closed__0 = (const lean_object*)&l_Lean_Parser_Command_grindPattern___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_grindPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_grindPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_grindPattern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_grindPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 150, 72, 45, 239, 118, 187, 30)}};
static const lean_object* l_Lean_Parser_Command_grindPattern___closed__1 = (const lean_object*)&l_Lean_Parser_Command_grindPattern___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__2;
static const lean_string_object l_Lean_Parser_Command_grindPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_pattern "};
static const lean_object* l_Lean_Parser_Command_grindPattern___closed__3 = (const lean_object*)&l_Lean_Parser_Command_grindPattern___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__4;
static const lean_string_object l_Lean_Parser_Command_grindPattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Command_grindPattern___closed__5 = (const lean_object*)&l_Lean_Parser_Command_grindPattern___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__6;
static const lean_string_object l_Lean_Parser_Command_grindPattern___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Command_grindPattern___closed__7 = (const lean_object*)&l_Lean_Parser_Command_grindPattern___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__11;
static const lean_string_object l_Lean_Parser_Command_grindPattern___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Command_grindPattern___closed__12 = (const lean_object*)&l_Lean_Parser_Command_grindPattern___closed__12_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__13;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__14;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__15;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__16;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__17;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__18;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__19;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__20;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__21;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__22;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__23;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern___closed__24;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4113, .m_capacity = 4113, .m_length = 4059, .m_data = "The `grind_pattern` command can be used to manually select a pattern for theorem instantiation.\nEnabling the option `trace.grind.ematch.instance` causes `grind` to print a trace message for each\ntheorem instance it generates, which can be helpful when determining patterns.\n\nWhen multiple patterns are specified together, all of them must match in the current context before\n`grind` attempts to instantiate the theorem. This is referred to as a *multi-pattern*.\nThis is useful for theorems such as transitivity rules, where multiple premises must be simultaneously\npresent for the rule to apply.\n\nIn the following example, `R` is a transitive binary relation over `Int`.\n```\nopaque R : Int → Int → Prop\naxiom Rtrans {x y z : Int} : R x y → R y z → R x z\n```\nTo use the fact that `R` is transitive, `grind` must already be able to satisfy both premises.\nThis is represented using a multi-pattern:\n```\ngrind_pattern Rtrans => R x y, R y z\n\nexample {a b c d} : R a b → R b c → R c d → R a d := by\n  grind\n```\nThe multi-pattern `R x y`, `R y z` instructs `grind` to instantiate `Rtrans` only when both `R x y`\nand `R y z` are available in the context. In the example, `grind` applies `Rtrans` to derive `R a c`\nfrom `R a b` and `R b c`, and can then repeat the same reasoning to deduce `R a d` from `R a c` and\n`R c d`.\n\nYou can add constraints to restrict theorem instantiation. For example:\n```\ngrind_pattern extract_extract => (as.extract i j).extract k l where\n  as =/= #[]\n```\nThe constraint instructs `grind` to instantiate the theorem only if `as` is **not** definitionally equal\nto `#[]`.\n\n## Constraints\n\n- `x =/= term`: The term bound to `x` (one of the theorem parameters) is **not** definitionally equal to `term`.\n  The term may contain holes (i.e., `_`).\n\n- `x =\?= term`: The term bound to `x` is definitionally equal to `term`.\n  The term may contain holes (i.e., `_`).\n\n- `size x < n`: The term bound to `x` has size less than `n`. Implicit arguments\nand binder types are ignored when computing the size.\n\n- `depth x < n`: The term bound to `x` has depth less than `n`.\n\n- `is_ground x`: The term bound to `x` does not contain local variables or meta-variables.\n\n- `is_value x`: The term bound to `x` is a value. That is, it is a constructor fully applied to value arguments,\na literal (`Nat`, `Int`, `String`, etc.), or a lambda `fun x => t`.\n\n- `is_strict_value x`: Similar to `is_value`, but without lambdas.\n\n- `not_value x`: The term bound to `x` is a **not** value (see `is_value`).\n\n- `not_strict_value x`: Similar to `not_value`, but without lambdas.\n\n- `gen < n`: The theorem instance has generation less than `n`. Recall that each term is assigned a\ngeneration, and terms produced by theorem instantiation have a generation that is one greater than\nthe maximal generation of all the terms used to instantiate the theorem. This constraint complements\nthe `gen` option available in `grind`.\n\n- `max_insts < n`: A new instance is generated only if less than `n` instances have been generated so far.\n\n- `guard e`: The instantiation is delayed until `grind` learns that `e` is `true` in this state.\n\n- `check e`: Similar to `guard e`, but `grind` checks whether `e` is implied by its current state by\nassuming `¬ e` and trying to deduce an inconsistency.\n\n## Example\n\nConsider the following example where `f` is a monotonic function\n```\nopaque f : Nat → Nat\naxiom fMono : x ≤ y → f x ≤ f y\n```\nand you want to instruct `grind` to instantiate `fMono` for every pair of terms `f x` and `f y` when\n`x ≤ y` and `x` is **not** definitionally equal to `y`. You can use\n```\ngrind_pattern fMono => f x, f y where\n  guard x ≤ y\n  x =/= y\n```\nThen, in the following example, only three instances are generated.\n```\n/--\ntrace: [grind.ematch.instance] fMono: a ≤ f a → f a ≤ f (f a)\n[grind.ematch.instance] fMono: f a ≤ f (f a) → f (f a) ≤ f (f (f a))\n[grind.ematch.instance] fMono: a ≤ f (f a) → f a ≤ f (f (f a))\n-/\n#guard_msgs in\nexample : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by\n  set_option trace.grind.ematch.instance true in\n  grind\n```"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 127, 91, 31, 152, 192, 239, 0)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 207, 54, 209, 125, 235, 59, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 167, 118, 192, 170, 54, 174, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 109, 181, 159, 253, 28, 20, 27)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 180, 19, 60, 251, 16, 248, 4)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 3, 137, 225, 191, 109, 15, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 251, 19, 154, 122, 46, 102, 83)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 181, 50, 148, 147, 18, 116, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 99, 47, 57, 220, 158, 80, 177)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 255, 184, 86, 170, 101, 94, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 251, 30, 194, 200, 196, 155, 146)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 98, 91, 194, 218, 242, 81, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 13, 145, 164, 157, 20, 85, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 28, 63, 140, 60, 95, 49, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 6, 178, 35, 133, 139, 189, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 122, 227, 73, 240, 180, 209, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 108, 68, 184, 240, 212, 209, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 64, 163, 182, 89, 157, 60, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 187, 126, 138, 230, 109, 238, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 159, 37, 255, 126, 171, 5, 31)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 211, 65, 46, 115, 168, 222, 235)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 192, 36, 119, 203, 72, 32, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 71, 120, 134, 181, 74, 206, 169)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 110, 209, 235, 108, 250, 182, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_atomic_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 16, 176, 15, 194, 80, 158, 173)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 115, 19, 158, 125, 134, 158, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value),((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 242, 154, 125, 67, 48, 229, 39)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 26, 141, 127, 162, 11, 105, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__0_value),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_attrKind_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__7_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__3_value),((lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__7_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_darrow_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__8 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__8_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__12_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__9 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__9_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_formatter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__12_value),((lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__10 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_formatter___closed__10_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__12;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__13;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__14;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__15;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__16;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__17;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_formatter___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_formatter___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 150, 72, 45, 239, 118, 187, 30)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 200, 156, 71, 131, 6, 95, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ident_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 127, 91, 31, 152, 192, 239, 0)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 84, 118, 176, 132, 117, 92, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 167, 118, 192, 170, 54, 174, 22)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 173, 46, 61, 60, 73, 66, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 180, 19, 60, 251, 16, 248, 4)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 215, 233, 47, 129, 189, 148, 31)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 251, 19, 154, 122, 46, 102, 83)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 201, 71, 176, 97, 157, 208, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 99, 47, 57, 220, 158, 80, 177)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 251, 121, 136, 184, 127, 75, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_numLit_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 251, 30, 194, 200, 196, 155, 146)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 143, 129, 42, 205, 242, 84, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 13, 145, 164, 157, 20, 85, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 14, 192, 203, 142, 140, 191, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 6, 178, 35, 133, 139, 189, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 96, 46, 27, 86, 180, 255, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 108, 68, 184, 240, 212, 209, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 170, 99, 54, 1, 237, 179, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_termParser_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 187, 126, 138, 230, 109, 238, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 49, 6, 241, 143, 192, 236, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_check___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 211, 65, 46, 115, 168, 222, 235)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 211, 114, 23, 49, 18, 80, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 71, 120, 134, 181, 74, 206, 169)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 191, 130, 132, 64, 159, 49, 2)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1_value)} };
static const lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 16, 176, 15, 194, 80, 158, 173)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 110, 103, 183, 49, 129, 106, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___boxed(lean_object*);
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value),((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ppLine_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5;
static lean_once_cell_t l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 242, 154, 125, 67, 48, 229, 39)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 64, 176, 27, 209, 1, 173, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__0_value),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_attrKind_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__7_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3_value),((lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_optional_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_darrow_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__12_value)} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9_value;
static const lean_closure_object l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepBy1_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__12_value),((lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10 = (const lean_object*)&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10_value;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17;
static lean_once_cell_t l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_grindPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 150, 72, 45, 239, 118, 187, 30)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 120, 140, 196, 156, 187, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_Command_initGrindNorm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "initGrindNorm"};
static const lean_object* l_Lean_Parser_Command_initGrindNorm___closed__0 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_initGrindNorm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 56, 244, 141, 180, 41, 47, 38)}};
static const lean_object* l_Lean_Parser_Command_initGrindNorm___closed__1 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__2;
static const lean_string_object l_Lean_Parser_Command_initGrindNorm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "init_grind_norm "};
static const lean_object* l_Lean_Parser_Command_initGrindNorm___closed__3 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__4;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__5;
static const lean_string_object l_Lean_Parser_Command_initGrindNorm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Parser_Command_initGrindNorm___closed__6 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__7;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__8;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__9;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__10;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__11;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__12;
static lean_once_cell_t l_Lean_Parser_Command_initGrindNorm___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Command_initGrindNorm___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__0_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__0 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__1 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__2 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__3 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__3_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__4 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__5 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__1_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__6 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_formatter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_leadingNode_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___closed__7 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_formatter___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 56, 244, 141, 180, 41, 47, 38)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 234, 40, 238, 223, 8, 255, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__0_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__3_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_many_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1_value),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6_value;
static const lean_closure_object l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6_value)} };
static const lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7 = (const lean_object*)&l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Command_initGrindNorm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 56, 244, 141, 180, 41, 47, 38)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 224, 224, 121, 79, 210, 11, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___boxed(lean_object*);
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__6(void){
_start:
{
uint8_t v___x_12_; uint8_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_12_ = 0;
v___x_13_ = 1;
v___x_14_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_15_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4));
v___x_16_ = l_Lean_Parser_mkAntiquot(v___x_15_, v___x_14_, v___x_13_, v___x_12_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__8(void){
_start:
{
uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = 0;
v___x_19_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__7));
v___x_20_ = l_Lean_Parser_nonReservedSymbol(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__10(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__9));
v___x_23_ = l_Lean_Parser_symbol(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__10, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__10_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__10);
v___x_25_ = l_Lean_Parser_optional(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__11, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11);
v___x_27_ = l_Lean_Parser_ident;
v___x_28_ = l_Lean_Parser_andthen(v___x_27_, v___x_26_);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__12, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12);
v___x_30_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__8, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__8);
v___x_31_ = l_Lean_Parser_andthen(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__14(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__13, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__13_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__13);
v___x_33_ = lean_unsigned_to_nat(1024u);
v___x_34_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_35_ = l_Lean_Parser_leadingNode(v___x_34_, v___x_33_, v___x_32_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__15(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__14, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__14_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__14);
v___x_37_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__6, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__6);
v___x_38_ = l_Lean_Parser_withAntiquot(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__16(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__15, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__15_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__15);
v___x_40_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_41_ = l_Lean_Parser_withCache(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isValue(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__16, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__16_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__16);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2(void){
_start:
{
uint8_t v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = 0;
v___x_51_ = 1;
v___x_52_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_53_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0));
v___x_54_ = l_Lean_Parser_mkAntiquot(v___x_53_, v___x_52_, v___x_51_, v___x_50_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4(void){
_start:
{
uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = 0;
v___x_57_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3));
v___x_58_ = l_Lean_Parser_nonReservedSymbol(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__12, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12);
v___x_60_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4, &l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4);
v___x_61_ = l_Lean_Parser_andthen(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5, &l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5);
v___x_63_ = lean_unsigned_to_nat(1024u);
v___x_64_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_65_ = l_Lean_Parser_leadingNode(v___x_64_, v___x_63_, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6, &l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6);
v___x_67_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2, &l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2);
v___x_68_ = l_Lean_Parser_withAntiquot(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7, &l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7);
v___x_70_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_71_ = l_Lean_Parser_withCache(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8, &l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__2(void){
_start:
{
uint8_t v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = 0;
v___x_81_ = 1;
v___x_82_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_83_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0));
v___x_84_ = l_Lean_Parser_mkAntiquot(v___x_83_, v___x_82_, v___x_81_, v___x_80_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__4(void){
_start:
{
uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = 0;
v___x_87_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__3));
v___x_88_ = l_Lean_Parser_nonReservedSymbol(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__5(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__12, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12);
v___x_90_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notValue___closed__4, &l_Lean_Parser_Command_GrindCnstr_notValue___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__4);
v___x_91_ = l_Lean_Parser_andthen(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__6(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notValue___closed__5, &l_Lean_Parser_Command_GrindCnstr_notValue___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__5);
v___x_93_ = lean_unsigned_to_nat(1024u);
v___x_94_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_95_ = l_Lean_Parser_leadingNode(v___x_94_, v___x_93_, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__7(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notValue___closed__6, &l_Lean_Parser_Command_GrindCnstr_notValue___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__6);
v___x_97_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notValue___closed__2, &l_Lean_Parser_Command_GrindCnstr_notValue___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__2);
v___x_98_ = l_Lean_Parser_withAntiquot(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__8(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notValue___closed__7, &l_Lean_Parser_Command_GrindCnstr_notValue___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__7);
v___x_100_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_101_ = l_Lean_Parser_withCache(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notValue(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notValue___closed__8, &l_Lean_Parser_Command_GrindCnstr_notValue___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__8);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2(void){
_start:
{
uint8_t v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = 0;
v___x_111_ = 1;
v___x_112_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_113_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0));
v___x_114_ = l_Lean_Parser_mkAntiquot(v___x_113_, v___x_112_, v___x_111_, v___x_110_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4(void){
_start:
{
uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = 0;
v___x_117_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3));
v___x_118_ = l_Lean_Parser_nonReservedSymbol(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__12, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12);
v___x_120_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4, &l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4);
v___x_121_ = l_Lean_Parser_andthen(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5, &l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5);
v___x_123_ = lean_unsigned_to_nat(1024u);
v___x_124_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_125_ = l_Lean_Parser_leadingNode(v___x_124_, v___x_123_, v___x_122_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6, &l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6);
v___x_127_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2, &l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2);
v___x_128_ = l_Lean_Parser_withAntiquot(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7, &l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7);
v___x_130_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_131_ = l_Lean_Parser_withCache(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8, &l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__2(void){
_start:
{
uint8_t v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_140_ = 0;
v___x_141_ = 1;
v___x_142_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_143_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0));
v___x_144_ = l_Lean_Parser_mkAntiquot(v___x_143_, v___x_142_, v___x_141_, v___x_140_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__4(void){
_start:
{
uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = 0;
v___x_147_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__3));
v___x_148_ = l_Lean_Parser_nonReservedSymbol(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__5(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__12, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12);
v___x_150_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isGround___closed__4, &l_Lean_Parser_Command_GrindCnstr_isGround___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__4);
v___x_151_ = l_Lean_Parser_andthen(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__6(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isGround___closed__5, &l_Lean_Parser_Command_GrindCnstr_isGround___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__5);
v___x_153_ = lean_unsigned_to_nat(1024u);
v___x_154_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_155_ = l_Lean_Parser_leadingNode(v___x_154_, v___x_153_, v___x_152_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__7(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isGround___closed__6, &l_Lean_Parser_Command_GrindCnstr_isGround___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__6);
v___x_157_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isGround___closed__2, &l_Lean_Parser_Command_GrindCnstr_isGround___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__2);
v___x_158_ = l_Lean_Parser_withAntiquot(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__8(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isGround___closed__7, &l_Lean_Parser_Command_GrindCnstr_isGround___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__7);
v___x_160_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_161_ = l_Lean_Parser_withCache(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_isGround(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isGround___closed__8, &l_Lean_Parser_Command_GrindCnstr_isGround___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__8);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2(void){
_start:
{
uint8_t v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = 0;
v___x_171_ = 1;
v___x_172_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_173_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0));
v___x_174_ = l_Lean_Parser_mkAntiquot(v___x_173_, v___x_172_, v___x_171_, v___x_170_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4(void){
_start:
{
uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = 0;
v___x_177_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3));
v___x_178_ = l_Lean_Parser_nonReservedSymbol(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5));
v___x_181_ = l_Lean_Parser_symbol(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__11, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11);
v___x_183_ = l_Lean_Parser_numLit;
v___x_184_ = l_Lean_Parser_andthen(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7);
v___x_186_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6);
v___x_187_ = l_Lean_Parser_andthen(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8);
v___x_189_ = l_Lean_Parser_ident;
v___x_190_ = l_Lean_Parser_andthen(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9);
v___x_192_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4);
v___x_193_ = l_Lean_Parser_andthen(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10);
v___x_195_ = lean_unsigned_to_nat(1024u);
v___x_196_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_197_ = l_Lean_Parser_leadingNode(v___x_196_, v___x_195_, v___x_194_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11);
v___x_199_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2);
v___x_200_ = l_Lean_Parser_withAntiquot(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12);
v___x_202_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_203_ = l_Lean_Parser_withCache(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_sizeLt(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2(void){
_start:
{
uint8_t v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_212_ = 0;
v___x_213_ = 1;
v___x_214_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_215_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0));
v___x_216_ = l_Lean_Parser_mkAntiquot(v___x_215_, v___x_214_, v___x_213_, v___x_212_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4(void){
_start:
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = 0;
v___x_219_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3));
v___x_220_ = l_Lean_Parser_nonReservedSymbol(v___x_219_, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9);
v___x_222_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4, &l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4);
v___x_223_ = l_Lean_Parser_andthen(v___x_222_, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_224_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5, &l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5);
v___x_225_ = lean_unsigned_to_nat(1024u);
v___x_226_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_227_ = l_Lean_Parser_leadingNode(v___x_226_, v___x_225_, v___x_224_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6, &l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6);
v___x_229_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2, &l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2);
v___x_230_ = l_Lean_Parser_withAntiquot(v___x_229_, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7, &l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7);
v___x_232_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_233_ = l_Lean_Parser_withCache(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_depthLt(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8, &l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__2(void){
_start:
{
uint8_t v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_242_ = 0;
v___x_243_ = 1;
v___x_244_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_245_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0));
v___x_246_ = l_Lean_Parser_mkAntiquot(v___x_245_, v___x_244_, v___x_243_, v___x_242_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__4(void){
_start:
{
uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = 0;
v___x_249_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__3));
v___x_250_ = l_Lean_Parser_nonReservedSymbol(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__5(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8);
v___x_252_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_genLt___closed__4, &l_Lean_Parser_Command_GrindCnstr_genLt___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__4);
v___x_253_ = l_Lean_Parser_andthen(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__6(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_genLt___closed__5, &l_Lean_Parser_Command_GrindCnstr_genLt___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__5);
v___x_255_ = lean_unsigned_to_nat(1024u);
v___x_256_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_257_ = l_Lean_Parser_leadingNode(v___x_256_, v___x_255_, v___x_254_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__7(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_genLt___closed__6, &l_Lean_Parser_Command_GrindCnstr_genLt___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__6);
v___x_259_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_genLt___closed__2, &l_Lean_Parser_Command_GrindCnstr_genLt___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__2);
v___x_260_ = l_Lean_Parser_withAntiquot(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__8(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_genLt___closed__7, &l_Lean_Parser_Command_GrindCnstr_genLt___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__7);
v___x_262_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_263_ = l_Lean_Parser_withCache(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_genLt(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_genLt___closed__8, &l_Lean_Parser_Command_GrindCnstr_genLt___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__8);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2(void){
_start:
{
uint8_t v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = 0;
v___x_273_ = 1;
v___x_274_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_275_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0));
v___x_276_ = l_Lean_Parser_mkAntiquot(v___x_275_, v___x_274_, v___x_273_, v___x_272_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4(void){
_start:
{
uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = 0;
v___x_279_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3));
v___x_280_ = l_Lean_Parser_nonReservedSymbol(v___x_279_, v___x_278_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8, &l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8);
v___x_282_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4, &l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4);
v___x_283_ = l_Lean_Parser_andthen(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_284_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5, &l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5);
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_286_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_287_ = l_Lean_Parser_leadingNode(v___x_286_, v___x_285_, v___x_284_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6, &l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6);
v___x_289_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2, &l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2);
v___x_290_ = l_Lean_Parser_withAntiquot(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7, &l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7);
v___x_292_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_293_ = l_Lean_Parser_withCache(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_maxInsts(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8, &l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__2(void){
_start:
{
uint8_t v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = 0;
v___x_303_ = 1;
v___x_304_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_305_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__0));
v___x_306_ = l_Lean_Parser_mkAntiquot(v___x_305_, v___x_304_, v___x_303_, v___x_302_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__4(void){
_start:
{
uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = 0;
v___x_309_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__3));
v___x_310_ = l_Lean_Parser_nonReservedSymbol(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__6(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__5));
v___x_313_ = l_Lean_Parser_checkColGe(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__7(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = l_Lean_Parser_termParser(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__8(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_isValue___closed__11, &l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once, _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11);
v___x_317_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__7, &l_Lean_Parser_Command_GrindCnstr_guard___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__7);
v___x_318_ = l_Lean_Parser_andthen(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__8, &l_Lean_Parser_Command_GrindCnstr_guard___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__8);
v___x_320_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__6, &l_Lean_Parser_Command_GrindCnstr_guard___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__6);
v___x_321_ = l_Lean_Parser_andthen(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__10(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__9, &l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9);
v___x_323_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__4);
v___x_324_ = l_Lean_Parser_andthen(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__11(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__10, &l_Lean_Parser_Command_GrindCnstr_guard___closed__10_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__10);
v___x_326_ = lean_unsigned_to_nat(1024u);
v___x_327_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_328_ = l_Lean_Parser_leadingNode(v___x_327_, v___x_326_, v___x_325_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__12(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__11, &l_Lean_Parser_Command_GrindCnstr_guard___closed__11_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__11);
v___x_330_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__2, &l_Lean_Parser_Command_GrindCnstr_guard___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__2);
v___x_331_ = l_Lean_Parser_withAntiquot(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__13(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__12, &l_Lean_Parser_Command_GrindCnstr_guard___closed__12_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__12);
v___x_333_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_334_ = l_Lean_Parser_withCache(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__13, &l_Lean_Parser_Command_GrindCnstr_guard___closed__13_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__13);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check___closed__2(void){
_start:
{
uint8_t v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_343_ = 0;
v___x_344_ = 1;
v___x_345_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_346_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__0));
v___x_347_ = l_Lean_Parser_mkAntiquot(v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check___closed__4(void){
_start:
{
uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = 0;
v___x_350_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__3));
v___x_351_ = l_Lean_Parser_nonReservedSymbol(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check___closed__5(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__9, &l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9);
v___x_353_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check___closed__4, &l_Lean_Parser_Command_GrindCnstr_check___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_check___closed__4);
v___x_354_ = l_Lean_Parser_andthen(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check___closed__6(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check___closed__5, &l_Lean_Parser_Command_GrindCnstr_check___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_check___closed__5);
v___x_356_ = lean_unsigned_to_nat(1024u);
v___x_357_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_358_ = l_Lean_Parser_leadingNode(v___x_357_, v___x_356_, v___x_355_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check___closed__7(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check___closed__6, &l_Lean_Parser_Command_GrindCnstr_check___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_check___closed__6);
v___x_360_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check___closed__2, &l_Lean_Parser_Command_GrindCnstr_check___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_check___closed__2);
v___x_361_ = l_Lean_Parser_withAntiquot(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check___closed__8(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check___closed__7, &l_Lean_Parser_Command_GrindCnstr_check___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_check___closed__7);
v___x_363_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_364_ = l_Lean_Parser_withCache(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check(void){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check___closed__8, &l_Lean_Parser_Command_GrindCnstr_check___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_check___closed__8);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2(void){
_start:
{
uint8_t v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_373_ = 0;
v___x_374_ = 1;
v___x_375_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_376_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0));
v___x_377_ = l_Lean_Parser_mkAntiquot(v___x_376_, v___x_375_, v___x_374_, v___x_373_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3));
v___x_380_ = l_Lean_Parser_symbol(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4);
v___x_382_ = l_Lean_Parser_ident;
v___x_383_ = l_Lean_Parser_andthen(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5);
v___x_385_ = l_Lean_Parser_atomic(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__9, &l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9);
v___x_387_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6);
v___x_388_ = l_Lean_Parser_andthen(v___x_387_, v___x_386_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7);
v___x_390_ = lean_unsigned_to_nat(1024u);
v___x_391_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_392_ = l_Lean_Parser_leadingNode(v___x_391_, v___x_390_, v___x_389_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8);
v___x_394_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2);
v___x_395_ = l_Lean_Parser_withAntiquot(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9);
v___x_397_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_398_ = l_Lean_Parser_withCache(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10, &l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__2(void){
_start:
{
uint8_t v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = 0;
v___x_408_ = 1;
v___x_409_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_410_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0));
v___x_411_ = l_Lean_Parser_mkAntiquot(v___x_410_, v___x_409_, v___x_408_, v___x_407_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__4(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__3));
v___x_414_ = l_Lean_Parser_symbol(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__5(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__4, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__4);
v___x_416_ = l_Lean_Parser_ident;
v___x_417_ = l_Lean_Parser_andthen(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__6(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__5, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__5);
v___x_419_ = l_Lean_Parser_atomic(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__7(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__9, &l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9);
v___x_421_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__6, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__6);
v___x_422_ = l_Lean_Parser_andthen(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__8(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__7, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__7);
v___x_424_ = lean_unsigned_to_nat(1024u);
v___x_425_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_426_ = l_Lean_Parser_leadingNode(v___x_425_, v___x_424_, v___x_423_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__9(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__8, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__8_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__8);
v___x_428_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__2, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__2);
v___x_429_ = l_Lean_Parser_withAntiquot(v___x_428_, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__10(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__9, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__9_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__9);
v___x_431_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_432_ = l_Lean_Parser_withCache(v___x_431_, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq___closed__10, &l_Lean_Parser_Command_GrindCnstr_defEq___closed__10_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__10);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__0(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_Parser_Command_GrindCnstr_defEq;
v___x_435_ = l_Lean_Parser_Command_GrindCnstr_notDefEq;
v___x_436_ = l_Lean_Parser_orelse(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__0, &l_Lean_Parser_Command_grindPatternCnstr___closed__0_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__0);
v___x_438_ = l_Lean_Parser_Command_GrindCnstr_check;
v___x_439_ = l_Lean_Parser_orelse(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__1, &l_Lean_Parser_Command_grindPatternCnstr___closed__1_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__1);
v___x_441_ = l_Lean_Parser_Command_GrindCnstr_guard;
v___x_442_ = l_Lean_Parser_orelse(v___x_441_, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__3(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__2, &l_Lean_Parser_Command_grindPatternCnstr___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__2);
v___x_444_ = l_Lean_Parser_Command_GrindCnstr_maxInsts;
v___x_445_ = l_Lean_Parser_orelse(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__4(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__3, &l_Lean_Parser_Command_grindPatternCnstr___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__3);
v___x_447_ = l_Lean_Parser_Command_GrindCnstr_genLt;
v___x_448_ = l_Lean_Parser_orelse(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__5(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__4, &l_Lean_Parser_Command_grindPatternCnstr___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__4);
v___x_450_ = l_Lean_Parser_Command_GrindCnstr_depthLt;
v___x_451_ = l_Lean_Parser_orelse(v___x_450_, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__6(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__5, &l_Lean_Parser_Command_grindPatternCnstr___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__5);
v___x_453_ = l_Lean_Parser_Command_GrindCnstr_sizeLt;
v___x_454_ = l_Lean_Parser_orelse(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__7(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__6, &l_Lean_Parser_Command_grindPatternCnstr___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__6);
v___x_456_ = l_Lean_Parser_Command_GrindCnstr_isGround;
v___x_457_ = l_Lean_Parser_orelse(v___x_456_, v___x_455_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__8(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__7, &l_Lean_Parser_Command_grindPatternCnstr___closed__7_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__7);
v___x_459_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue;
v___x_460_ = l_Lean_Parser_orelse(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__9(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__8, &l_Lean_Parser_Command_grindPatternCnstr___closed__8_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__8);
v___x_462_ = l_Lean_Parser_Command_GrindCnstr_notValue;
v___x_463_ = l_Lean_Parser_orelse(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__10(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__9, &l_Lean_Parser_Command_grindPatternCnstr___closed__9_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__9);
v___x_465_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue;
v___x_466_ = l_Lean_Parser_orelse(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr___closed__11(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__10, &l_Lean_Parser_Command_grindPatternCnstr___closed__10_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__10);
v___x_468_ = l_Lean_Parser_Command_GrindCnstr_isValue;
v___x_469_ = l_Lean_Parser_orelse(v___x_468_, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr___closed__11, &l_Lean_Parser_Command_grindPatternCnstr___closed__11_once, _init_l_Lean_Parser_Command_grindPatternCnstr___closed__11);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__2(void){
_start:
{
uint8_t v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = 0;
v___x_478_ = 1;
v___x_479_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_480_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__0));
v___x_481_ = l_Lean_Parser_mkAntiquot(v___x_480_, v___x_479_, v___x_478_, v___x_477_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__4(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__3));
v___x_484_ = l_Lean_Parser_symbol(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__5(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_Parser_Command_grindPatternCnstr;
v___x_486_ = l_Lean_Parser_skip;
v___x_487_ = l_Lean_Parser_andthen(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__6(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__5, &l_Lean_Parser_Command_grindPatternCnstrs___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__5);
v___x_489_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__6, &l_Lean_Parser_Command_GrindCnstr_guard___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__6);
v___x_490_ = l_Lean_Parser_andthen(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__7(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__6, &l_Lean_Parser_Command_grindPatternCnstrs___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__6);
v___x_492_ = l_Lean_Parser_many1(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__8(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__7, &l_Lean_Parser_Command_grindPatternCnstrs___closed__7_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__7);
v___x_494_ = l_Lean_Parser_withPosition(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__9(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__8, &l_Lean_Parser_Command_grindPatternCnstrs___closed__8_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__8);
v___x_496_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__4, &l_Lean_Parser_Command_grindPatternCnstrs___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__4);
v___x_497_ = l_Lean_Parser_andthen(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__10(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__9, &l_Lean_Parser_Command_grindPatternCnstrs___closed__9_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__9);
v___x_499_ = lean_unsigned_to_nat(1024u);
v___x_500_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_501_ = l_Lean_Parser_leadingNode(v___x_500_, v___x_499_, v___x_498_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__11(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__10, &l_Lean_Parser_Command_grindPatternCnstrs___closed__10_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__10);
v___x_503_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__2, &l_Lean_Parser_Command_grindPatternCnstrs___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__2);
v___x_504_ = l_Lean_Parser_withAntiquot(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__12(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__11, &l_Lean_Parser_Command_grindPatternCnstrs___closed__11_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__11);
v___x_506_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_507_ = l_Lean_Parser_withCache(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs(void){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs___closed__12, &l_Lean_Parser_Command_grindPatternCnstrs___closed__12_once, _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__12);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__2(void){
_start:
{
uint8_t v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_515_ = 0;
v___x_516_ = 1;
v___x_517_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_518_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__0));
v___x_519_ = l_Lean_Parser_mkAntiquot(v___x_518_, v___x_517_, v___x_516_, v___x_515_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__4(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__3));
v___x_522_ = l_Lean_Parser_symbol(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__6(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__5));
v___x_525_ = l_Lean_Parser_symbol(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__8(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__7));
v___x_528_ = l_Lean_Parser_symbol(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__9(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__8, &l_Lean_Parser_Command_grindPattern___closed__8_once, _init_l_Lean_Parser_Command_grindPattern___closed__8);
v___x_530_ = l_Lean_Parser_ident;
v___x_531_ = l_Lean_Parser_andthen(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__10(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__9, &l_Lean_Parser_Command_grindPattern___closed__9_once, _init_l_Lean_Parser_Command_grindPattern___closed__9);
v___x_533_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__6, &l_Lean_Parser_Command_grindPattern___closed__6_once, _init_l_Lean_Parser_Command_grindPattern___closed__6);
v___x_534_ = l_Lean_Parser_andthen(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__11(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__10, &l_Lean_Parser_Command_grindPattern___closed__10_once, _init_l_Lean_Parser_Command_grindPattern___closed__10);
v___x_536_ = l_Lean_Parser_optional(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__13(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__12));
v___x_539_ = l_Lean_Parser_symbol(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__14(void){
_start:
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_540_ = 0;
v___x_541_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__13, &l_Lean_Parser_Command_grindPattern___closed__13_once, _init_l_Lean_Parser_Command_grindPattern___closed__13);
v___x_542_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__12));
v___x_543_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard___closed__7, &l_Lean_Parser_Command_GrindCnstr_guard___closed__7_once, _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__7);
v___x_544_ = l_Lean_Parser_sepBy1(v___x_543_, v___x_542_, v___x_541_, v___x_540_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__15(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = l_Lean_Parser_Command_grindPatternCnstrs;
v___x_546_ = l_Lean_Parser_optional(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__16(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__15, &l_Lean_Parser_Command_grindPattern___closed__15_once, _init_l_Lean_Parser_Command_grindPattern___closed__15);
v___x_548_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__14, &l_Lean_Parser_Command_grindPattern___closed__14_once, _init_l_Lean_Parser_Command_grindPattern___closed__14);
v___x_549_ = l_Lean_Parser_andthen(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__17(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__16, &l_Lean_Parser_Command_grindPattern___closed__16_once, _init_l_Lean_Parser_Command_grindPattern___closed__16);
v___x_551_ = l_Lean_Parser_darrow;
v___x_552_ = l_Lean_Parser_andthen(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__18(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__17, &l_Lean_Parser_Command_grindPattern___closed__17_once, _init_l_Lean_Parser_Command_grindPattern___closed__17);
v___x_554_ = l_Lean_Parser_ident;
v___x_555_ = l_Lean_Parser_andthen(v___x_554_, v___x_553_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__19(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__18, &l_Lean_Parser_Command_grindPattern___closed__18_once, _init_l_Lean_Parser_Command_grindPattern___closed__18);
v___x_557_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__11, &l_Lean_Parser_Command_grindPattern___closed__11_once, _init_l_Lean_Parser_Command_grindPattern___closed__11);
v___x_558_ = l_Lean_Parser_andthen(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__20(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__19, &l_Lean_Parser_Command_grindPattern___closed__19_once, _init_l_Lean_Parser_Command_grindPattern___closed__19);
v___x_560_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__4, &l_Lean_Parser_Command_grindPattern___closed__4_once, _init_l_Lean_Parser_Command_grindPattern___closed__4);
v___x_561_ = l_Lean_Parser_andthen(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__21(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__20, &l_Lean_Parser_Command_grindPattern___closed__20_once, _init_l_Lean_Parser_Command_grindPattern___closed__20);
v___x_563_ = l_Lean_Parser_Term_attrKind;
v___x_564_ = l_Lean_Parser_andthen(v___x_563_, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__22(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__21, &l_Lean_Parser_Command_grindPattern___closed__21_once, _init_l_Lean_Parser_Command_grindPattern___closed__21);
v___x_566_ = lean_unsigned_to_nat(1024u);
v___x_567_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_568_ = l_Lean_Parser_leadingNode(v___x_567_, v___x_566_, v___x_565_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__23(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__22, &l_Lean_Parser_Command_grindPattern___closed__22_once, _init_l_Lean_Parser_Command_grindPattern___closed__22);
v___x_570_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__2, &l_Lean_Parser_Command_grindPattern___closed__2_once, _init_l_Lean_Parser_Command_grindPattern___closed__2);
v___x_571_ = l_Lean_Parser_withAntiquot(v___x_570_, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern___closed__24(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__23, &l_Lean_Parser_Command_grindPattern___closed__23_once, _init_l_Lean_Parser_Command_grindPattern___closed__23);
v___x_573_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_574_ = l_Lean_Parser_withCache(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern___closed__24, &l_Lean_Parser_Command_grindPattern___closed__24_once, _init_l_Lean_Parser_Command_grindPattern___closed__24);
return v___x_575_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1(){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1));
v___x_581_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_582_ = l_Lean_Parser_Command_grindPattern;
v___x_583_ = lean_unsigned_to_nat(1000u);
v___x_584_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_580_, v___x_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_585_;
v_res_585_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___boxed(lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
return v_res_587_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3(){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0));
v___x_592_ = l_Lean_addBuiltinDocString(v___x_590_, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_593_;
v_res_593_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___boxed(lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
return v_res_595_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter(lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0));
v___x_628_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7));
v___x_629_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_627_, v___x_628_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_isValue_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_622_ = stack[0].m_obj;
lean_object* v_a_623_ = stack[1].m_obj;
lean_object* v_a_624_ = stack[2].m_obj;
lean_object* v_a_625_ = stack[3].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter(v_a_622_, v_a_623_, v_a_624_, v_a_625_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed(lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter(v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
return v_res_636_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7(){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_646_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_647_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1));
v___x_649_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed), 5, 0);
v___x_650_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_646_, v___x_647_, v___x_648_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_651_;
v_res_651_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___boxed(lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
return v_res_653_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0));
v___x_678_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3));
v___x_679_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_677_, v___x_678_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_679_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_672_ = stack[0].m_obj;
lean_object* v_a_673_ = stack[1].m_obj;
lean_object* v_a_674_ = stack[2].m_obj;
lean_object* v_a_675_ = stack[3].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(v_a_672_, v_a_673_, v_a_674_, v_a_675_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed(lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_686_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11(){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_696_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0));
v___x_698_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed), 5, 0);
v___x_699_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_695_, v___x_696_, v___x_697_, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_700_;
v_res_700_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___boxed(lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
return v_res_702_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter(lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0));
v___x_727_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3));
v___x_728_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_726_, v___x_727_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
return v___x_728_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notValue_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_721_ = stack[0].m_obj;
lean_object* v_a_722_ = stack[1].m_obj;
lean_object* v_a_723_ = stack[2].m_obj;
lean_object* v_a_724_ = stack[3].m_obj;
lean_object* v_res_729_;
v_res_729_ = l_Lean_Parser_Command_GrindCnstr_notValue_formatter(v_a_721_, v_a_722_, v_a_723_, v_a_724_);
stack->m_obj
 = v_res_729_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed(lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Parser_Command_GrindCnstr_notValue_formatter(v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_735_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15(){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_744_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_745_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0));
v___x_747_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed), 5, 0);
v___x_748_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_744_, v___x_745_, v___x_746_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_749_;
v_res_749_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
stack->m_obj
 = v_res_749_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___boxed(lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
return v_res_751_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0));
v___x_776_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3));
v___x_777_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_775_, v___x_776_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_777_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_770_ = stack[0].m_obj;
lean_object* v_a_771_ = stack[1].m_obj;
lean_object* v_a_772_ = stack[2].m_obj;
lean_object* v_a_773_ = stack[3].m_obj;
lean_object* v_res_778_;
v_res_778_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(v_a_770_, v_a_771_, v_a_772_, v_a_773_);
stack->m_obj
 = v_res_778_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed(lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_784_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19(){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_793_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_794_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0));
v___x_796_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed), 5, 0);
v___x_797_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_793_, v___x_794_, v___x_795_, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_798_;
v_res_798_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___boxed(lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
return v_res_800_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter(lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0));
v___x_825_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3));
v___x_826_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_824_, v___x_825_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_826_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_isGround_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_819_ = stack[0].m_obj;
lean_object* v_a_820_ = stack[1].m_obj;
lean_object* v_a_821_ = stack[2].m_obj;
lean_object* v_a_822_ = stack[3].m_obj;
lean_object* v_res_827_;
v_res_827_ = l_Lean_Parser_Command_GrindCnstr_isGround_formatter(v_a_819_, v_a_820_, v_a_821_, v_a_822_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed(lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Parser_Command_GrindCnstr_isGround_formatter(v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_833_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23(){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_842_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_843_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0));
v___x_845_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed), 5, 0);
v___x_846_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_842_, v___x_843_, v___x_844_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_847_;
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___boxed(lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
return v_res_849_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0));
v___x_886_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8));
v___x_887_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_885_, v___x_886_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
return v___x_887_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_880_ = stack[0].m_obj;
lean_object* v_a_881_ = stack[1].m_obj;
lean_object* v_a_882_ = stack[2].m_obj;
lean_object* v_a_883_ = stack[3].m_obj;
lean_object* v_res_888_;
v_res_888_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(v_a_880_, v_a_881_, v_a_882_, v_a_883_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed(lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_894_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27(){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_903_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_904_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0));
v___x_906_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed), 5, 0);
v___x_907_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_903_, v___x_904_, v___x_905_, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_908_;
v_res_908_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___boxed(lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
return v_res_910_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0));
v___x_935_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3));
v___x_936_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_934_, v___x_935_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_936_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_depthLt_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_929_ = stack[0].m_obj;
lean_object* v_a_930_ = stack[1].m_obj;
lean_object* v_a_931_ = stack[2].m_obj;
lean_object* v_a_932_ = stack[3].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(v_a_929_, v_a_930_, v_a_931_, v_a_932_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed(lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_943_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31(){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_952_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_953_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0));
v___x_955_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed), 5, 0);
v___x_956_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_952_, v___x_953_, v___x_954_, v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_957_;
v_res_957_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___boxed(lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
return v_res_959_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter(lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0));
v___x_984_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3));
v___x_985_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_983_, v___x_984_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_985_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_genLt_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_978_ = stack[0].m_obj;
lean_object* v_a_979_ = stack[1].m_obj;
lean_object* v_a_980_ = stack[2].m_obj;
lean_object* v_a_981_ = stack[3].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_Lean_Parser_Command_GrindCnstr_genLt_formatter(v_a_978_, v_a_979_, v_a_980_, v_a_981_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed(lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Parser_Command_GrindCnstr_genLt_formatter(v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
return v_res_992_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35(){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1001_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1002_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0));
v___x_1004_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed), 5, 0);
v___x_1005_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1001_, v___x_1002_, v___x_1003_, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1006_;
v_res_1006_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___boxed(lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
return v_res_1008_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0));
v___x_1033_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3));
v___x_1034_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1032_, v___x_1033_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1034_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1027_ = stack[0].m_obj;
lean_object* v_a_1028_ = stack[1].m_obj;
lean_object* v_a_1029_ = stack[2].m_obj;
lean_object* v_a_1030_ = stack[3].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed(lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1041_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39(){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1050_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1051_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0));
v___x_1053_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed), 5, 0);
v___x_1054_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1050_, v___x_1051_, v___x_1052_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1055_;
v_res_1055_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
stack->m_obj
 = v_res_1055_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___boxed(lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
return v_res_1057_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3));
v___x_1075_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
v___x_1076_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1076_, 0, v___x_1075_);
lean_closure_set(v___x_1076_, 1, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1078_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1));
v___x_1079_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1079_, 0, v___x_1078_);
lean_closure_set(v___x_1079_, 1, v___x_1077_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5);
v___x_1081_ = lean_unsigned_to_nat(1024u);
v___x_1082_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1083_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1083_, 0, v___x_1082_);
lean_closure_set(v___x_1083_, 1, v___x_1081_);
lean_closure_set(v___x_1083_, 2, v___x_1080_);
return v___x_1083_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter(lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0));
v___x_1090_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6);
v___x_1091_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1089_, v___x_1090_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1091_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_guard_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1084_ = stack[0].m_obj;
lean_object* v_a_1085_ = stack[1].m_obj;
lean_object* v_a_1086_ = stack[2].m_obj;
lean_object* v_a_1087_ = stack[3].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed(lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter(v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
return v_res_1098_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43(){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1107_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1108_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0));
v___x_1110_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed), 5, 0);
v___x_1111_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1107_, v___x_1108_, v___x_1109_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1112_;
v_res_1112_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
stack->m_obj
 = v_res_1112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___boxed(lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
return v_res_1114_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1127_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1));
v___x_1128_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1128_, 0, v___x_1127_);
lean_closure_set(v___x_1128_, 1, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2, &l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2);
v___x_1130_ = lean_unsigned_to_nat(1024u);
v___x_1131_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1132_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1132_, 0, v___x_1131_);
lean_closure_set(v___x_1132_, 1, v___x_1130_);
lean_closure_set(v___x_1132_, 2, v___x_1129_);
return v___x_1132_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter(lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0));
v___x_1139_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3, &l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3);
v___x_1140_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1138_, v___x_1139_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1140_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_check_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1133_ = stack[0].m_obj;
lean_object* v_a_1134_ = stack[1].m_obj;
lean_object* v_a_1135_ = stack[2].m_obj;
lean_object* v_a_1136_ = stack[3].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_Parser_Command_GrindCnstr_check_formatter(v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed(lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Parser_Command_GrindCnstr_check_formatter(v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1147_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47(){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1157_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0));
v___x_1159_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed), 5, 0);
v___x_1160_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1156_, v___x_1157_, v___x_1158_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1161_;
v_res_1161_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___boxed(lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
return v_res_1163_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1179_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3));
v___x_1180_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1180_, 0, v___x_1179_);
lean_closure_set(v___x_1180_, 1, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4);
v___x_1182_ = lean_unsigned_to_nat(1024u);
v___x_1183_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_1184_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1184_, 0, v___x_1183_);
lean_closure_set(v___x_1184_, 1, v___x_1182_);
lean_closure_set(v___x_1184_, 2, v___x_1181_);
return v___x_1184_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0));
v___x_1191_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5, &l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5);
v___x_1192_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1190_, v___x_1191_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1192_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1185_ = stack[0].m_obj;
lean_object* v_a_1186_ = stack[1].m_obj;
lean_object* v_a_1187_ = stack[2].m_obj;
lean_object* v_a_1188_ = stack[3].m_obj;
lean_object* v_res_1193_;
v_res_1193_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
stack->m_obj
 = v_res_1193_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed(lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1199_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51(){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1208_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1209_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_1210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0));
v___x_1211_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed), 5, 0);
v___x_1212_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1208_, v___x_1209_, v___x_1210_, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1213_;
v_res_1213_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___boxed(lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
return v_res_1215_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4);
v___x_1231_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3));
v___x_1232_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1232_, 0, v___x_1231_);
lean_closure_set(v___x_1232_, 1, v___x_1230_);
return v___x_1232_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4, &l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4);
v___x_1234_ = lean_unsigned_to_nat(1024u);
v___x_1235_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_1236_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1236_, 0, v___x_1235_);
lean_closure_set(v___x_1236_, 1, v___x_1234_);
lean_closure_set(v___x_1236_, 2, v___x_1233_);
return v___x_1236_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter(lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0));
v___x_1243_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5, &l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5);
v___x_1244_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1242_, v___x_1243_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
return v___x_1244_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_defEq_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1237_ = stack[0].m_obj;
lean_object* v_a_1238_ = stack[1].m_obj;
lean_object* v_a_1239_ = stack[2].m_obj;
lean_object* v_a_1240_ = stack[3].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l_Lean_Parser_Command_GrindCnstr_defEq_formatter(v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed(lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Parser_Command_GrindCnstr_defEq_formatter(v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
return v_res_1251_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55(){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1260_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1261_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_1262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0));
v___x_1263_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed), 5, 0);
v___x_1264_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1260_, v___x_1261_, v___x_1262_, v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1265_;
v_res_1265_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___boxed(lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
return v_res_1267_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed), 5, 0);
v___x_1269_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed), 5, 0);
v___x_1270_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1270_, 0, v___x_1269_);
lean_closure_set(v___x_1270_, 1, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0);
v___x_1272_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed), 5, 0);
v___x_1273_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1273_, 0, v___x_1272_);
lean_closure_set(v___x_1273_, 1, v___x_1271_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1);
v___x_1275_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed), 5, 0);
v___x_1276_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1276_, 0, v___x_1275_);
lean_closure_set(v___x_1276_, 1, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2);
v___x_1278_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed), 5, 0);
v___x_1279_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1279_, 0, v___x_1278_);
lean_closure_set(v___x_1279_, 1, v___x_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3);
v___x_1281_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed), 5, 0);
v___x_1282_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1282_, 0, v___x_1281_);
lean_closure_set(v___x_1282_, 1, v___x_1280_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4);
v___x_1284_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed), 5, 0);
v___x_1285_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1285_, 0, v___x_1284_);
lean_closure_set(v___x_1285_, 1, v___x_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5);
v___x_1287_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed), 5, 0);
v___x_1288_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1288_, 0, v___x_1287_);
lean_closure_set(v___x_1288_, 1, v___x_1286_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6);
v___x_1290_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed), 5, 0);
v___x_1291_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1291_, 0, v___x_1290_);
lean_closure_set(v___x_1291_, 1, v___x_1289_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7);
v___x_1293_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed), 5, 0);
v___x_1294_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1294_, 0, v___x_1293_);
lean_closure_set(v___x_1294_, 1, v___x_1292_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8);
v___x_1296_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed), 5, 0);
v___x_1297_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1297_, 0, v___x_1296_);
lean_closure_set(v___x_1297_, 1, v___x_1295_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9);
v___x_1299_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed), 5, 0);
v___x_1300_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_1300_, 0, v___x_1299_);
lean_closure_set(v___x_1300_, 1, v___x_1298_);
return v___x_1300_;
}
}
lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter(lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed), 5, 0);
v___x_1307_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10, &l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10_once, _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10);
v___x_1308_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1306_, v___x_1307_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1308_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_grindPatternCnstr_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1301_ = stack[0].m_obj;
lean_object* v_a_1302_ = stack[1].m_obj;
lean_object* v_a_1303_ = stack[2].m_obj;
lean_object* v_a_1304_ = stack[3].m_obj;
lean_object* v_res_1309_;
v_res_1309_ = l_Lean_Parser_Command_grindPatternCnstr_formatter(v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
stack->m_obj
 = v_res_1309_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed(lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Parser_Command_grindPatternCnstr_formatter(v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1315_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed), 5, 0);
v___x_1326_ = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
v___x_1327_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1327_, 0, v___x_1326_);
lean_closure_set(v___x_1327_, 1, v___x_1325_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2);
v___x_1329_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_formatter___boxed), 6, 1);
lean_closure_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3);
v___x_1331_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1));
v___x_1332_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1332_, 0, v___x_1331_);
lean_closure_set(v___x_1332_, 1, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4);
v___x_1334_ = lean_unsigned_to_nat(1024u);
v___x_1335_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_1336_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1336_, 0, v___x_1335_);
lean_closure_set(v___x_1336_, 1, v___x_1334_);
lean_closure_set(v___x_1336_, 2, v___x_1333_);
return v___x_1336_;
}
}
lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0));
v___x_1343_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5, &l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5);
v___x_1344_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1342_, v___x_1343_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1344_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_grindPatternCnstrs_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1337_ = stack[0].m_obj;
lean_object* v_a_1338_ = stack[1].m_obj;
lean_object* v_a_1339_ = stack[2].m_obj;
lean_object* v_a_1340_ = stack[3].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l_Lean_Parser_Command_grindPatternCnstrs_formatter(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed(lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Parser_Command_grindPatternCnstrs_formatter(v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
return v_res_1351_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61(){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1359_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1360_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_1361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0));
v___x_1362_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed), 5, 0);
v___x_1363_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1359_, v___x_1360_, v___x_1361_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1364_;
v_res_1364_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___boxed(lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
return v_res_1366_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__11(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed), 5, 0);
v___x_1399_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter___boxed), 6, 1);
lean_closure_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__12(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__11, &l_Lean_Parser_Command_grindPattern_formatter___closed__11_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__11);
v___x_1401_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__10));
v___x_1402_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1402_, 0, v___x_1401_);
lean_closure_set(v___x_1402_, 1, v___x_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__13(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__12, &l_Lean_Parser_Command_grindPattern_formatter___closed__12_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__12);
v___x_1404_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__8));
v___x_1405_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1405_, 0, v___x_1404_);
lean_closure_set(v___x_1405_, 1, v___x_1403_);
return v___x_1405_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__14(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__13, &l_Lean_Parser_Command_grindPattern_formatter___closed__13_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__13);
v___x_1407_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2));
v___x_1408_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1408_, 0, v___x_1407_);
lean_closure_set(v___x_1408_, 1, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__15(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__14, &l_Lean_Parser_Command_grindPattern_formatter___closed__14_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__14);
v___x_1410_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__7));
v___x_1411_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1411_, 0, v___x_1410_);
lean_closure_set(v___x_1411_, 1, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__16(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__15, &l_Lean_Parser_Command_grindPattern_formatter___closed__15_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__15);
v___x_1413_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__2));
v___x_1414_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1414_, 0, v___x_1413_);
lean_closure_set(v___x_1414_, 1, v___x_1412_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__17(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__16, &l_Lean_Parser_Command_grindPattern_formatter___closed__16_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__16);
v___x_1416_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__1));
v___x_1417_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_1417_, 0, v___x_1416_);
lean_closure_set(v___x_1417_, 1, v___x_1415_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_formatter___closed__18(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1418_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__17, &l_Lean_Parser_Command_grindPattern_formatter___closed__17_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__17);
v___x_1419_ = lean_unsigned_to_nat(1024u);
v___x_1420_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_1421_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(v___x_1421_, 0, v___x_1420_);
lean_closure_set(v___x_1421_, 1, v___x_1419_);
lean_closure_set(v___x_1421_, 2, v___x_1418_);
return v___x_1421_;
}
}
lean_object* l_Lean_Parser_Command_grindPattern_formatter(lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_formatter___closed__0));
v___x_1428_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_formatter___closed__18, &l_Lean_Parser_Command_grindPattern_formatter___closed__18_once, _init_l_Lean_Parser_Command_grindPattern_formatter___closed__18);
v___x_1429_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_1427_, v___x_1428_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
return v___x_1429_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_grindPattern_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1422_ = stack[0].m_obj;
lean_object* v_a_1423_ = stack[1].m_obj;
lean_object* v_a_1424_ = stack[2].m_obj;
lean_object* v_a_1425_ = stack[3].m_obj;
lean_object* v_res_1430_;
v_res_1430_ = l_Lean_Parser_Command_grindPattern_formatter(v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
stack->m_obj
 = v_res_1430_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_formatter___boxed(lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Parser_Command_grindPattern_formatter(v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1436_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65(){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1444_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1445_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0));
v___x_1447_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPattern_formatter___boxed), 5, 0);
v___x_1448_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1444_, v___x_1445_, v___x_1446_, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1449_;
v_res_1449_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___boxed(lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
return v_res_1451_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0));
v___x_1484_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7));
v___x_1485_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1483_, v___x_1484_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
return v___x_1485_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1478_ = stack[0].m_obj;
lean_object* v_a_1479_ = stack[1].m_obj;
lean_object* v_a_1480_ = stack[2].m_obj;
lean_object* v_a_1481_ = stack[3].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed(lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1492_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69(){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1502_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1503_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5));
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1));
v___x_1505_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed), 5, 0);
v___x_1506_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1502_, v___x_1503_, v___x_1504_, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1507_;
v_res_1507_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___boxed(lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
return v_res_1509_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0));
v___x_1534_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3));
v___x_1535_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1533_, v___x_1534_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1528_ = stack[0].m_obj;
lean_object* v_a_1529_ = stack[1].m_obj;
lean_object* v_a_1530_ = stack[2].m_obj;
lean_object* v_a_1531_ = stack[3].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed(lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1542_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73(){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1551_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1552_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1));
v___x_1553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0));
v___x_1554_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed), 5, 0);
v___x_1555_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1551_, v___x_1552_, v___x_1553_, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1556_;
v_res_1556_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
stack->m_obj
 = v_res_1556_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___boxed(lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
return v_res_1558_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0));
v___x_1583_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3));
v___x_1584_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1582_, v___x_1583_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1584_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1577_ = stack[0].m_obj;
lean_object* v_a_1578_ = stack[1].m_obj;
lean_object* v_a_1579_ = stack[2].m_obj;
lean_object* v_a_1580_ = stack[3].m_obj;
lean_object* v_res_1585_;
v_res_1585_ = l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
stack->m_obj
 = v_res_1585_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed(lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1591_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77(){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1600_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1601_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1));
v___x_1602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0));
v___x_1603_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed), 5, 0);
v___x_1604_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1600_, v___x_1601_, v___x_1602_, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1605_;
v_res_1605_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___boxed(lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
return v_res_1607_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0));
v___x_1632_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3));
v___x_1633_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1631_, v___x_1632_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1626_ = stack[0].m_obj;
lean_object* v_a_1627_ = stack[1].m_obj;
lean_object* v_a_1628_ = stack[2].m_obj;
lean_object* v_a_1629_ = stack[3].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed(lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1640_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81(){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1649_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1650_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1));
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0));
v___x_1652_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed), 5, 0);
v___x_1653_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1649_, v___x_1650_, v___x_1651_, v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1654_;
v_res_1654_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___boxed(lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
return v_res_1656_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0));
v___x_1681_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3));
v___x_1682_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1680_, v___x_1681_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
return v___x_1682_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1675_ = stack[0].m_obj;
lean_object* v_a_1676_ = stack[1].m_obj;
lean_object* v_a_1677_ = stack[2].m_obj;
lean_object* v_a_1678_ = stack[3].m_obj;
lean_object* v_res_1683_;
v_res_1683_ = l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
stack->m_obj
 = v_res_1683_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed(lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1689_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85(){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1698_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1699_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1));
v___x_1700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0));
v___x_1701_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed), 5, 0);
v___x_1702_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1698_, v___x_1699_, v___x_1700_, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1703_;
v_res_1703_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
stack->m_obj
 = v_res_1703_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___boxed(lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
return v_res_1705_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0));
v___x_1742_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8));
v___x_1743_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1741_, v___x_1742_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
return v___x_1743_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1736_ = stack[0].m_obj;
lean_object* v_a_1737_ = stack[1].m_obj;
lean_object* v_a_1738_ = stack[2].m_obj;
lean_object* v_a_1739_ = stack[3].m_obj;
lean_object* v_res_1744_;
v_res_1744_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
stack->m_obj
 = v_res_1744_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed(lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1750_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89(){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1759_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1760_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1));
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0));
v___x_1762_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed), 5, 0);
v___x_1763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1759_, v___x_1760_, v___x_1761_, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1764_;
v_res_1764_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
stack->m_obj
 = v_res_1764_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___boxed(lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
return v_res_1766_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0));
v___x_1791_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3));
v___x_1792_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1790_, v___x_1791_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1792_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1785_ = stack[0].m_obj;
lean_object* v_a_1786_ = stack[1].m_obj;
lean_object* v_a_1787_ = stack[2].m_obj;
lean_object* v_a_1788_ = stack[3].m_obj;
lean_object* v_res_1793_;
v_res_1793_ = l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
stack->m_obj
 = v_res_1793_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed(lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1799_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93(){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1808_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1809_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1));
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0));
v___x_1811_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed), 5, 0);
v___x_1812_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1808_, v___x_1809_, v___x_1810_, v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1813_;
v_res_1813_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
stack->m_obj
 = v_res_1813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___boxed(lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
return v_res_1815_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0));
v___x_1840_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3));
v___x_1841_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1839_, v___x_1840_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1841_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1834_ = stack[0].m_obj;
lean_object* v_a_1835_ = stack[1].m_obj;
lean_object* v_a_1836_ = stack[2].m_obj;
lean_object* v_a_1837_ = stack[3].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed(lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
return v_res_1848_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97(){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1857_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1858_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1));
v___x_1859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0));
v___x_1860_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed), 5, 0);
v___x_1861_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1857_, v___x_1858_, v___x_1859_, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1862_;
v_res_1862_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
stack->m_obj
 = v_res_1862_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
return v_res_1864_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0));
v___x_1889_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3));
v___x_1890_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1888_, v___x_1889_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1883_ = stack[0].m_obj;
lean_object* v_a_1884_ = stack[1].m_obj;
lean_object* v_a_1885_ = stack[2].m_obj;
lean_object* v_a_1886_ = stack[3].m_obj;
lean_object* v_res_1891_;
v_res_1891_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
stack->m_obj
 = v_res_1891_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed(lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1897_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101(){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1906_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1907_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1));
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0));
v___x_1909_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed), 5, 0);
v___x_1910_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1906_, v___x_1907_, v___x_1908_, v___x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1911_;
v_res_1911_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
stack->m_obj
 = v_res_1911_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___boxed(lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
return v_res_1913_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3));
v___x_1931_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
v___x_1932_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1932_, 0, v___x_1931_);
lean_closure_set(v___x_1932_, 1, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___x_1934_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1));
v___x_1935_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1935_, 0, v___x_1934_);
lean_closure_set(v___x_1935_, 1, v___x_1933_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5);
v___x_1937_ = lean_unsigned_to_nat(1024u);
v___x_1938_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1939_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1939_, 0, v___x_1938_);
lean_closure_set(v___x_1939_, 1, v___x_1937_);
lean_closure_set(v___x_1939_, 2, v___x_1936_);
return v___x_1939_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0));
v___x_1946_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6);
v___x_1947_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1945_, v___x_1946_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_1947_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1940_ = stack[0].m_obj;
lean_object* v_a_1941_ = stack[1].m_obj;
lean_object* v_a_1942_ = stack[2].m_obj;
lean_object* v_a_1943_ = stack[3].m_obj;
lean_object* v_res_1948_;
v_res_1948_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
stack->m_obj
 = v_res_1948_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed(lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1954_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105(){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1963_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1964_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_guard___closed__1));
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0));
v___x_1966_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed), 5, 0);
v___x_1967_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1963_, v___x_1964_, v___x_1965_, v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1968_;
v_res_1968_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
stack->m_obj
 = v_res_1968_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___boxed(lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
return v_res_1970_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___x_1983_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1));
v___x_1984_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_1984_, 0, v___x_1983_);
lean_closure_set(v___x_1984_, 1, v___x_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1985_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2, &l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2_once, _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2);
v___x_1986_ = lean_unsigned_to_nat(1024u);
v___x_1987_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_1988_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_1988_, 0, v___x_1987_);
lean_closure_set(v___x_1988_, 1, v___x_1986_);
lean_closure_set(v___x_1988_, 2, v___x_1985_);
return v___x_1988_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0));
v___x_1995_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3, &l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3);
v___x_1996_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_1994_, v___x_1995_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
return v___x_1996_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_check_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1989_ = stack[0].m_obj;
lean_object* v_a_1990_ = stack[1].m_obj;
lean_object* v_a_1991_ = stack[2].m_obj;
lean_object* v_a_1992_ = stack[3].m_obj;
lean_object* v_res_1997_;
v_res_1997_ = l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
stack->m_obj
 = v_res_1997_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed(lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2003_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109(){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2012_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2013_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_check___closed__1));
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0));
v___x_2015_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed), 5, 0);
v___x_2016_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2012_, v___x_2013_, v___x_2014_, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2017_;
v_res_2017_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___boxed(lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
return v_res_2019_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2020_, v___x_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2020_ = stack[0].m_obj;
lean_object* v___x_2021_ = stack[1].m_obj;
lean_object* v___y_2022_ = stack[2].m_obj;
lean_object* v___y_2023_ = stack[3].m_obj;
lean_object* v___y_2024_ = stack[4].m_obj;
lean_object* v___y_2025_ = stack[5].m_obj;
lean_object* v_res_2028_;
v_res_2028_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(v___x_2020_, v___x_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
stack->m_obj
 = v_res_2028_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed(lean_object* v___x_2029_, lean_object* v___x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(v___x_2029_, v___x_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___f_2050_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2));
v___x_2051_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2051_, 0, v___f_2050_);
lean_closure_set(v___x_2051_, 1, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3, &l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3);
v___x_2053_ = lean_unsigned_to_nat(1024u);
v___x_2054_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_2055_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2055_, 0, v___x_2054_);
lean_closure_set(v___x_2055_, 1, v___x_2053_);
lean_closure_set(v___x_2055_, 2, v___x_2052_);
return v___x_2055_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0));
v___x_2062_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4);
v___x_2063_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2061_, v___x_2062_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
return v___x_2063_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2056_ = stack[0].m_obj;
lean_object* v_a_2057_ = stack[1].m_obj;
lean_object* v_a_2058_ = stack[2].m_obj;
lean_object* v_a_2059_ = stack[3].m_obj;
lean_object* v_res_2064_;
v_res_2064_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
stack->m_obj
 = v_res_2064_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed(lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
return v_res_2070_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113(){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2079_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2080_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1));
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0));
v___x_2082_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed), 5, 0);
v___x_2083_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2079_, v___x_2080_, v___x_2081_, v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2084_;
v_res_2084_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
stack->m_obj
 = v_res_2084_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___boxed(lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
return v_res_2086_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4);
v___f_2100_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2));
v___x_2101_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2101_, 0, v___f_2100_);
lean_closure_set(v___x_2101_, 1, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3, &l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3);
v___x_2103_ = lean_unsigned_to_nat(1024u);
v___x_2104_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_2105_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2105_, 0, v___x_2104_);
lean_closure_set(v___x_2105_, 1, v___x_2103_);
lean_closure_set(v___x_2105_, 2, v___x_2102_);
return v___x_2105_;
}
}
lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0));
v___x_2112_ = lean_obj_once(&l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4, &l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4);
v___x_2113_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2111_, v___x_2112_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2113_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2106_ = stack[0].m_obj;
lean_object* v_a_2107_ = stack[1].m_obj;
lean_object* v_a_2108_ = stack[2].m_obj;
lean_object* v_a_2109_ = stack[3].m_obj;
lean_object* v_res_2114_;
v_res_2114_ = l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
stack->m_obj
 = v_res_2114_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed(lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2120_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117(){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2129_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2130_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1));
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0));
v___x_2132_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed), 5, 0);
v___x_2133_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2134_;
v_res_2134_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
stack->m_obj
 = v_res_2134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___boxed(lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed), 5, 0);
v___x_2138_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed), 5, 0);
v___x_2139_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2139_, 0, v___x_2138_);
lean_closure_set(v___x_2139_, 1, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0);
v___x_2141_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed), 5, 0);
v___x_2142_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2142_, 0, v___x_2141_);
lean_closure_set(v___x_2142_, 1, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1);
v___x_2144_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed), 5, 0);
v___x_2145_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2145_, 0, v___x_2144_);
lean_closure_set(v___x_2145_, 1, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2);
v___x_2147_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed), 5, 0);
v___x_2148_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2148_, 0, v___x_2147_);
lean_closure_set(v___x_2148_, 1, v___x_2146_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3);
v___x_2150_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed), 5, 0);
v___x_2151_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2151_, 0, v___x_2150_);
lean_closure_set(v___x_2151_, 1, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4);
v___x_2153_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed), 5, 0);
v___x_2154_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2154_, 0, v___x_2153_);
lean_closure_set(v___x_2154_, 1, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5);
v___x_2156_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed), 5, 0);
v___x_2157_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2157_, 0, v___x_2156_);
lean_closure_set(v___x_2157_, 1, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6);
v___x_2159_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed), 5, 0);
v___x_2160_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2160_, 0, v___x_2159_);
lean_closure_set(v___x_2160_, 1, v___x_2158_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7);
v___x_2162_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed), 5, 0);
v___x_2163_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2163_, 0, v___x_2162_);
lean_closure_set(v___x_2163_, 1, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8);
v___x_2165_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed), 5, 0);
v___x_2166_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2166_, 0, v___x_2165_);
lean_closure_set(v___x_2166_, 1, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9);
v___x_2168_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed), 5, 0);
v___x_2169_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2169_, 0, v___x_2168_);
lean_closure_set(v___x_2169_, 1, v___x_2167_);
return v___x_2169_;
}
}
lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed), 5, 0);
v___x_2176_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10, &l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10_once, _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10);
v___x_2177_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2175_, v___x_2176_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
return v___x_2177_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_grindPatternCnstr_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2170_ = stack[0].m_obj;
lean_object* v_a_2171_ = stack[1].m_obj;
lean_object* v_a_2172_ = stack[2].m_obj;
lean_object* v_a_2173_ = stack[3].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed(lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2184_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed), 5, 0);
v___x_2196_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2));
v___x_2197_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2197_, 0, v___x_2196_);
lean_closure_set(v___x_2197_, 1, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3);
v___x_2199_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4);
v___x_2201_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1));
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2202_, 0, v___x_2201_);
lean_closure_set(v___x_2202_, 1, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5);
v___x_2204_ = lean_unsigned_to_nat(1024u);
v___x_2205_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_2206_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2206_, 0, v___x_2205_);
lean_closure_set(v___x_2206_, 1, v___x_2204_);
lean_closure_set(v___x_2206_, 2, v___x_2203_);
return v___x_2206_;
}
}
lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0));
v___x_2213_ = lean_obj_once(&l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6, &l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6_once, _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6);
v___x_2214_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2212_, v___x_2213_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
return v___x_2214_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2207_ = stack[0].m_obj;
lean_object* v_a_2208_ = stack[1].m_obj;
lean_object* v_a_2209_ = stack[2].m_obj;
lean_object* v_a_2210_ = stack[3].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed(lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
return v_res_2221_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123(){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2229_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2230_ = ((lean_object*)(l_Lean_Parser_Command_grindPatternCnstrs___closed__1));
v___x_2231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0));
v___x_2232_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed), 5, 0);
v___x_2233_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2229_, v___x_2230_, v___x_2231_, v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2234_;
v_res_2234_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
stack->m_obj
 = v_res_2234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___boxed(lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
return v_res_2236_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed), 5, 0);
v___x_2269_ = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11);
v___x_2271_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10));
v___x_2272_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2272_, 0, v___x_2271_);
lean_closure_set(v___x_2272_, 1, v___x_2270_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12);
v___x_2274_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8));
v___x_2275_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2275_, 0, v___x_2274_);
lean_closure_set(v___x_2275_, 1, v___x_2273_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13);
v___x_2277_ = ((lean_object*)(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2));
v___x_2278_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2278_, 0, v___x_2277_);
lean_closure_set(v___x_2278_, 1, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14);
v___x_2280_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7));
v___x_2281_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2281_, 0, v___x_2280_);
lean_closure_set(v___x_2281_, 1, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15);
v___x_2283_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2));
v___x_2284_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2284_, 0, v___x_2283_);
lean_closure_set(v___x_2284_, 1, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16);
v___x_2286_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1));
v___x_2287_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2287_, 0, v___x_2286_);
lean_closure_set(v___x_2287_, 1, v___x_2285_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2288_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17);
v___x_2289_ = lean_unsigned_to_nat(1024u);
v___x_2290_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_2291_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2291_, 0, v___x_2290_);
lean_closure_set(v___x_2291_, 1, v___x_2289_);
lean_closure_set(v___x_2291_, 2, v___x_2288_);
return v___x_2291_;
}
}
lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer(lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0));
v___x_2298_ = lean_obj_once(&l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18, &l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18_once, _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18);
v___x_2299_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2297_, v___x_2298_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2299_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_grindPattern_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2292_ = stack[0].m_obj;
lean_object* v_a_2293_ = stack[1].m_obj;
lean_object* v_a_2294_ = stack[2].m_obj;
lean_object* v_a_2295_ = stack[3].m_obj;
lean_object* v_res_2300_;
v_res_2300_ = l_Lean_Parser_Command_grindPattern_parenthesizer(v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
stack->m_obj
 = v_res_2300_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindPattern_parenthesizer___boxed(lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Parser_Command_grindPattern_parenthesizer(v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
return v_res_2306_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127(){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2314_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2315_ = ((lean_object*)(l_Lean_Parser_Command_grindPattern___closed__1));
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0));
v___x_2317_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_grindPattern_parenthesizer___boxed), 5, 0);
v___x_2318_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2314_, v___x_2315_, v___x_2316_, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2319_;
v_res_2319_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___boxed(lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
return v_res_2321_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__2(void){
_start:
{
uint8_t v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2328_ = 0;
v___x_2329_ = 1;
v___x_2330_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2331_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__0));
v___x_2332_ = l_Lean_Parser_mkAntiquot(v___x_2331_, v___x_2330_, v___x_2329_, v___x_2328_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__4(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__3));
v___x_2335_ = l_Lean_Parser_symbol(v___x_2334_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__5(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = l_Lean_Parser_ident;
v___x_2337_ = l_Lean_Parser_many(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__7(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__6));
v___x_2340_ = l_Lean_Parser_symbol(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__8(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__5, &l_Lean_Parser_Command_initGrindNorm___closed__5_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__5);
v___x_2342_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__7, &l_Lean_Parser_Command_initGrindNorm___closed__7_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__7);
v___x_2343_ = l_Lean_Parser_andthen(v___x_2342_, v___x_2341_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__9(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__8, &l_Lean_Parser_Command_initGrindNorm___closed__8_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__8);
v___x_2345_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__5, &l_Lean_Parser_Command_initGrindNorm___closed__5_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__5);
v___x_2346_ = l_Lean_Parser_andthen(v___x_2345_, v___x_2344_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__10(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__9, &l_Lean_Parser_Command_initGrindNorm___closed__9_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__9);
v___x_2348_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__4, &l_Lean_Parser_Command_initGrindNorm___closed__4_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__4);
v___x_2349_ = l_Lean_Parser_andthen(v___x_2348_, v___x_2347_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__11(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__10, &l_Lean_Parser_Command_initGrindNorm___closed__10_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__10);
v___x_2351_ = lean_unsigned_to_nat(1024u);
v___x_2352_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2353_ = l_Lean_Parser_leadingNode(v___x_2352_, v___x_2351_, v___x_2350_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__12(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__11, &l_Lean_Parser_Command_initGrindNorm___closed__11_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__11);
v___x_2355_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__2, &l_Lean_Parser_Command_initGrindNorm___closed__2_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__2);
v___x_2356_ = l_Lean_Parser_withAntiquot(v___x_2355_, v___x_2354_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm___closed__13(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__12, &l_Lean_Parser_Command_initGrindNorm___closed__12_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__12);
v___x_2358_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2359_ = l_Lean_Parser_withCache(v___x_2358_, v___x_2357_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lean_Parser_Command_initGrindNorm(void){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_obj_once(&l_Lean_Parser_Command_initGrindNorm___closed__13, &l_Lean_Parser_Command_initGrindNorm___closed__13_once, _init_l_Lean_Parser_Command_initGrindNorm___closed__13);
return v___x_2360_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1(){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1));
v___x_2363_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2364_ = l_Lean_Parser_Command_initGrindNorm;
v___x_2365_ = lean_unsigned_to_nat(1000u);
v___x_2366_ = l_Lean_Parser_addBuiltinLeadingParser(v___x_2362_, v___x_2363_, v___x_2364_, v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2367_;
v_res_2367_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
stack->m_obj
 = v_res_2367_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1___boxed(lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
return v_res_2369_;
}
}
lean_object* l_Lean_Parser_Command_initGrindNorm_formatter(lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_formatter___closed__0));
v___x_2402_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_formatter___closed__7));
v___x_2403_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2401_, v___x_2402_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2403_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_initGrindNorm_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2396_ = stack[0].m_obj;
lean_object* v_a_2397_ = stack[1].m_obj;
lean_object* v_a_2398_ = stack[2].m_obj;
lean_object* v_a_2399_ = stack[3].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l_Lean_Parser_Command_initGrindNorm_formatter(v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_formatter___boxed(lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Parser_Command_initGrindNorm_formatter(v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5(){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2418_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_2419_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0));
v___x_2421_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_initGrindNorm_formatter___boxed), 5, 0);
v___x_2422_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2418_, v___x_2419_, v___x_2420_, v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2423_;
v_res_2423_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
stack->m_obj
 = v_res_2423_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___boxed(lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
return v_res_2425_;
}
}
lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer(lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0));
v___x_2458_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7));
v___x_2459_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2457_, v___x_2458_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
return v___x_2459_;
}
}
LEAN_EXPORT void l_Lean_Parser_Command_initGrindNorm_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2452_ = stack[0].m_obj;
lean_object* v_a_2453_ = stack[1].m_obj;
lean_object* v_a_2454_ = stack[2].m_obj;
lean_object* v_a_2455_ = stack[3].m_obj;
lean_object* v_res_2460_;
v_res_2460_ = l_Lean_Parser_Command_initGrindNorm_parenthesizer(v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
stack->m_obj
 = v_res_2460_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed(lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Parser_Command_initGrindNorm_parenthesizer(v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2466_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9(){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2474_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_2475_ = ((lean_object*)(l_Lean_Parser_Command_initGrindNorm___closed__1));
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0));
v___x_2477_ = lean_alloc_closure((void*)(l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed), 5, 0);
v___x_2478_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2474_, v___x_2475_, v___x_2476_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2479_;
v_res_2479_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
stack->m_obj
 = v_res_2479_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___boxed(lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
return v_res_2481_;
}
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Command_GrindCnstr_isValue = _init_l_Lean_Parser_Command_GrindCnstr_isValue();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_isValue);
l_Lean_Parser_Command_GrindCnstr_isStrictValue = _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_isStrictValue);
l_Lean_Parser_Command_GrindCnstr_notValue = _init_l_Lean_Parser_Command_GrindCnstr_notValue();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_notValue);
l_Lean_Parser_Command_GrindCnstr_notStrictValue = _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_notStrictValue);
l_Lean_Parser_Command_GrindCnstr_isGround = _init_l_Lean_Parser_Command_GrindCnstr_isGround();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_isGround);
l_Lean_Parser_Command_GrindCnstr_sizeLt = _init_l_Lean_Parser_Command_GrindCnstr_sizeLt();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_sizeLt);
l_Lean_Parser_Command_GrindCnstr_depthLt = _init_l_Lean_Parser_Command_GrindCnstr_depthLt();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_depthLt);
l_Lean_Parser_Command_GrindCnstr_genLt = _init_l_Lean_Parser_Command_GrindCnstr_genLt();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_genLt);
l_Lean_Parser_Command_GrindCnstr_maxInsts = _init_l_Lean_Parser_Command_GrindCnstr_maxInsts();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_maxInsts);
l_Lean_Parser_Command_GrindCnstr_guard = _init_l_Lean_Parser_Command_GrindCnstr_guard();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_guard);
l_Lean_Parser_Command_GrindCnstr_check = _init_l_Lean_Parser_Command_GrindCnstr_check();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_check);
l_Lean_Parser_Command_GrindCnstr_notDefEq = _init_l_Lean_Parser_Command_GrindCnstr_notDefEq();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_notDefEq);
l_Lean_Parser_Command_GrindCnstr_defEq = _init_l_Lean_Parser_Command_GrindCnstr_defEq();
lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_defEq);
l_Lean_Parser_Command_grindPatternCnstr = _init_l_Lean_Parser_Command_grindPatternCnstr();
lean_mark_persistent(l_Lean_Parser_Command_grindPatternCnstr);
l_Lean_Parser_Command_grindPatternCnstrs = _init_l_Lean_Parser_Command_grindPatternCnstrs();
lean_mark_persistent(l_Lean_Parser_Command_grindPatternCnstrs);
l_Lean_Parser_Command_grindPattern = _init_l_Lean_Parser_Command_grindPattern();
lean_mark_persistent(l_Lean_Parser_Command_grindPattern);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Command_initGrindNorm = _init_l_Lean_Parser_Command_initGrindNorm();
lean_mark_persistent(l_Lean_Parser_Command_initGrindNorm);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
